# Handover: QPex Audit Hub, NCOB Box Audit IMEI cross-check

## 0. Working notes
- **Project:** `QPex_Audit_Hub_V9_08082026`, with `QPex_Audit_Latest.py` (a Flask app on port 7900, about 3,300 lines) and `templates/*.html`.
- **Scope:** the user only uses **NCOB Box Audit** (`audit_type == 'hl_box_audit'`). Everything else is out of scope.
- **Environment limits:** bash.exe doesn't work on the user's laptop, so don't use Bash. The `py_compile` check also couldn't be run. **All Stage 1 edits are unrun and untested against the live servers.**
- **Two copies exist.** The edits were made in the copy on Desktop (`...\Desktop\Claude Projects\...`). The user runs from a copy under `Downloads\...`, so changed files must be copied across.

## 1. Problem statement
Auditors scan an NCOB box, then each product. For serialized products (mobiles, tablets, computers, some earbuds and monitors) they scan a **WSN** and then an **IMEI/serial**. The user wants:

1. The scanned IMEI always checked against the IMEI recorded in **Flo-Lite**.
2. Any discrepancy between **FLO portal** data and **Flo-Lite** data flagged when that product is scanned, as an error popup ("Flo-Lite IMEI Mismatch") with an alien-style red row, like other alien products.
3. Multiple units of one WID: every unit's IMEI is checked; one mismatch makes the item an error.
4. Flo-Lite failure must **block the audit**, not degrade silently.
5. No dependence on `Inventory.csv`, `serialized_fsn.csv` or FSN-prefix guessing for NCOB.

## 2. How the app works today
- **Login:** Selenium drives Chrome to log into FLO (`http://10.24.1.53`) and Flo-Lite (`http://10.24.1.71/flo-lite`). The first 3 logins each day join a shared **pool** of Selenium sessions (`NCOB_POOL_SIZE`). Others get no personal browser. NCOB box scans use a pool driver.
- **`/scan_box`:** fetches the box contents once from Flo-Lite and keeps them in memory (`context["df"]`). Per-scan, `/scan_product` makes no network call, except `/api/verify_wsn` for serialized units. That does one FLO `get_location` GET per WSN (cached 10 minutes).
- **`/finalise`:** saves to SQLite `audit_database.db` (`master_audit_log`) and CSVs in `output_csv_files/`.
- **Serialized flow (frontend `templates/index_unit.html`):** the popup scans the WSN, calls `/api/verify_wsn` (FLO lookup), then IMEI1 (checked client-side against FLO's serial; IMEI2 only if IMEI1 doesn't match). `/scan_product` re-checks on the server and **rejects** on a FLO mismatch.
- **Original popup trigger:** `is_serialized_fsn()` looked the FSN up in `serialized_fsn.csv`, or used the prefixes `MOB` and `COM` if `ENABLE_SERIALIZED_FSN_CSV` is False. That flag is True and the CSV doesn't exist, so **no popup ever appeared**.

## 3. Data sources, endpoints and what was found

All calls go over HTTP with the pool driver's cookies. Flo-Lite headers: `csrf-token` (from a `<meta>` tag), `x-facility-id` (e.g. `jai_sh_wh_nl_01nl`), `x-tenant-id`, `x-client-id: WH`, and `x-proxy-user` on the outbound-picking proxy.

| # | Endpoint | Used for | Key facts |
|---|---|---|---|
| 1 | `GET /flo-lite-routes-api/psd-controller-routes/api/v1/container/{box}/details?use_case_context=VIEW_BOX_PAGE` (existing) | Box items | One entry per unit for serialized items. Fields: `fsn`, `wid`, `quantity`, `product_title`, `eans`, **`wsn`** (null for non-serialized), `group_references`, **`picking_reference_id`** (the PL id, null on some boxes). **No IMEI.** Bare calls without the app's header set return 500. |
| 2 | `GET /flo-lite-routes-api/outbound-picking-proxy/api/v3.0/picklists/{PL}` (new) | **Flo-Lite IMEI/serial** | The whole transfer list, e.g. 191 items across 12 boxes and 351 KB, about 140-350 ms. Each `picklistItems[]` row has `attributes.fsn/wid/wsn/isSerialized/serialNumberCount`, `status` (skip `CANCELLED`), `destinationLocationId` (matches `containerDetails[].id`, whose `label` is the box id), and the **serial in `prePickActions[FACT_COLLECT].responseData.serialNumbers`**. |
| 3 | `POST .../outbound-picking-proxy/api/v3.0/containers/details/label/{box}` body `{"externalPicklistId": "PL..."}` | Alternative found early | Returns `imeiSequence` per item (no usable WSN). **Not used**; the picklist GET replaces it. |
| 4 | `GET http://10.24.1.53/inventory/get_location?display_id={WSN}&searchbtn=Search` (FLO, existing) | FLO serial | Parsed via `_parse_wsn_location_html` ("Return Serial Numbers", Title, FSN). **Do not change**; the substring rule stays. |

**Findings that shaped the design**
- **`isSerialized` and `wsn` agree.** `isSerialized` is true exactly where a WSN exists. `serialNumberCount` says how many serials Flo-Lite collected (0 for some earbuds and monitors, 1 otherwise).
- **Serial formats differ by type.** Mobiles have a 15-digit Luhn-valid IMEI. Tablets, computers, monitors and earbuds have alphanumeric serials of 8, 10 or 20 characters (mixed even within one tablet FSN).
- **WSN alone is not a safe key.** The same WSN appeared on two completed picklist rows with different serials, but in different boxes. The reliable scoping is box label (via `destinationLocationId`) plus the WSN from details. Group reference (`TAI...nRES_m`) also pairs units once a trailing 16-hex suffix is stripped, but it's unused.
- **Unit counts match.** For every box tested, `details` WSNs matched the picklist rows 1:1 (B0USDWUK 10/10, B0V1FCPY 5/5).
- **FLO's `get_location` only works for units still in the warehouse.** For units in dispatched boxes it returns "No Shard defined for entity_id: ''". The user confirmed the lookup works before dispatch. Dispatched test boxes can't be used to test the FLO side.
- **A prefix rule would be wrong.** `ACC` has serialized and non-serialized items; `MOB`, `TAB`, `COM` and `MON` mostly are serialized.

## 4. Decisions made with the user
1. Flo-Lite's `isSerialized`/WSN drives the popup, not the prefix or CSV.
2. Flo-Lite is the reference serial; FLO is untouched and uses the existing "contains" rule.
3. **The auditor still scans WSN, then IMEI.**
4. Units with `serialNumberCount 0` are captured by **WSN only**.
5. **Fail closed.** The picklist call (8 s timeout, one retry) happens at box scan and any gap rejects the box. The Selenium scrape fallback is **dropped**.
6. Mismatches **flag and continue**: red row, a click-to-dismiss popup, and the reason saved. The existing FLO-vs-scanned rejection stays.
7. Build in 3 stages; the first is done.

## 5. Stage 1 (done, untested): what changed and where

**`QPex_Audit_Latest.py`**
- **New Flo-Lite helpers** (after `_build_flolite_api_session`):
  - `FloLiteDataError`, `PICKLIST_URL`, `picklist_cache` with a 30-minute TTL.
  - `_flolite_get_details`, `_parse_picklist_units`, `get_picklist_units` (one retry with fresh cookies), `_build_box_units`, and `load_ncob_box`.
  - `_build_flolite_api_session` now sets `s.proxy_user` and `s.facility_id`.
  - The old `api_get_container_details` and its debug JSON dump are **removed**.
- **`/scan_box`, NCOB branch:** calls `load_ncob_box`, returns a 502 error JSON on `FloLiteDataError`, and builds `context["units"]` (WSN -> `{fsn, wid, serials, serial_required}`) and `context["serial_fsns"]`. The DOM-scrape fallback is deleted. `scanner()` and `scan_box` reset the new context fields.
- **New helpers:** `fsn_is_serialized(context, fsn)` and `lookup_box_unit(context, wsn, fsn)`. They replace `is_serialized_fsn` in `/scan_product`, `get_shortages` and `/finalise`.
- **`/api/verify_wsn`:** the response now includes `in_box` and `serial_required`. It uses `context["pending_serial_fsn"]`, which `/scan_product` sets when it asks for the popup.
- **`/scan_product` serialized block:**
  - WSN-only path when `serial_required` is false.
  - `serial_mismatch` now needs a scanned serial (`... and bool(scanned_serials)`).
  - Non-blocking flags: "WSN not in this box", "Flo-Lite IMEI Mismatch" (scanned IMEI != Flo-Lite's) and "IMEI mismatch in FLO" (FLO serial doesn't contain Flo-Lite's).
  - Reasons go into `scanned_items[...]["wsn_mismatched"/"wsn_mismatch_reason"]` and the status suffix.
  - The response carries `flag_reason`.
- **Logs and DB:**
  - Serialized scans are now logged to `serialized_scan_log_v2.csv` with "Flo-Lite Serial" and "Flags". This file name is new so old columns don't misalign.
  - `master_audit_log` gains "Flo-Lite IMEI" and "IMEI Check", added by `init_db` and written in `/finalise`.
  - Status text is extended in `/finalise`, and `generate_cq_report` counts the flags as a Misshipment.
- **Login:** the `Inventory.csv` 25-hour freshness gate was removed. It blocked every login (any LDAP) once the file was stale or missing.

**`templates/index_unit.html`**
- New `#flag_modal` and `showFlagModal()`. It swallows all keystrokes while open, so scanner input can't dismiss it. It is used for box-load errors and for flags.
- `getRowClass` renders the flags red (`excess-misship`).
- `verifyWsnScanned` warns when the WSN isn't in the box and, when `serial_required === false`, saves straight after the WSN.

## 6. Request profile (after Stage 1)
- **Per box scan:** details (1 call, about 170-290 ms). Plus the picklist (1 call, about 140-350 ms) **only if** the box has serialized units, and **not repeated** for other boxes from the same transfer list within 30 minutes.
- **Per product scan:** no Flo-Lite calls. One FLO GET per serialized unit's WSN (cached 10 minutes).
- Nothing is fetched per FSN.

## 7. Remaining stages
- **Stage 2 (speed), not started:**
  - Cache cookies and CSRF per pool driver (about 10 minutes, refresh on 401/403) in `_build_flolite_api_session`, which currently reads `driver.page_source` each time.
  - Remove `driver.get(target_url)` plus `time.sleep(1.5)` for NCOB in `/scan_box`. **Careful:** that page load is also where the CSRF `<meta>` token comes from, so Stage 2 must keep a token source.
  - Acquire the pool driver only when the cookie cache is cold, which would remove lock contention between auditors.
- **Stage 3 (cleanup), not started:**
  - Remove the other 9 audit types and their routes and templates, the `Inventory.csv` loader, `serialized_fsn.csv` and `Audit_List.csv` logic, and the catalogue/FPDF features.
  - **Open decision:** `/scan_product` uses `Inventory.csv` to classify a product that isn't in the box as `MISSHIP` (known product) or `ALIEN` (unknown) (the "UNIVERSAL GLOBAL INVENTORY LOOKUP" block). Without the CSV an unmatched scan falls through as `EXCESS`. The user must choose: treat everything not in the box as `ALIEN`, or keep the CSV for that split.

## 8. Blockers, risks and untested points
1. **Nothing has been run.** No syntax check, no live test. Run the app and scan one serialized box first.
2. **Picklist call headers are unverified live.** `x-tenant-id: FKI` and `x-proxy-user` are sent, taken from the **pool worker's** Flo-Lite cookie, falling back to the lowercased session LDAP. If Flo-Lite requires the auditor's own identity, non-pool users' box scans could fail with "picklist ... could not be loaded (HTTP 4xx)". The error text includes the status code.
3. **FLO's serial format for tablets and computers is unknown.** It can only be seen on units that aren't dispatched yet. The v2 CSV logs both serials per scan, so the first live scans will show it. The "contains" rule is expected to work but is unconfirmed for 8-20 character serials.
4. **Strictness of the box block.** Any inconsistency (a duplicate WSN in the picklist, an FSN mismatch, a missing serial where one is expected) rejects the whole box by design.
5. **Empty FLO serial with a Flo-Lite serial present** is not flagged (the existing rule treats an empty FLO serial as nothing to compare). Flag it later if the user wants.
6. **No automated tests exist.** The parser `_parse_picklist_units` is the part worth testing, with the captured JSON.

## 9. Test boxes and reference data the user supplied
- **B0USDWUK** (10 mobiles, picklist `PL562950357743680`), **B0UZQOWG** (1 mobile; WSN `2J8EKY_R` also appears in another box with a different serial), **B0V1FCPY** (5 tablets, serials 8 or 20 characters), **B0V466GU** (computers), **B0UU6P8O** (cosmetics, no picklist ID).
- Warehouse: "Jaipur HL Sourcing Hub" maps to `jai_sh_wh_nl_01nl` in `WH_List.csv`.
