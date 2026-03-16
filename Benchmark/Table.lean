-- 1. Helper: Pad strings to a specific width
def padRight (s : String) (width : Nat) : String :=
  if s.length >= width then s
  else s ++ "".pushn ' ' (width - s.length)

-- 2. Helper: Ensure every row has the same number of columns as the headers
def normalizeRow (row : List String) (targetLen : Nat) : List String :=
  if row.length >= targetLen then
    row.take targetLen -- Truncate if too long
  else
    row ++ List.replicate (targetLen - row.length) "" -- Pad if too short
-- 3. Helper: Center a string within a specific width
def center (s : String) (width : Nat) : String :=
  if s.length >= width then s
  else
    let padding := width - s.length
    let left := padding / 2
    "".pushn ' ' left ++ s
-- 3. The Main Function with Configurable limits
-- We use Option Nat for the limits. 'none' means "show all".
def printTable (headers : List String) (rows : List (List String))
    (maxRows : Option Nat := none)
    (maxCols : Option Nat := none)
    (caption : Option String := none): IO Unit := do

  -- A. Apply Column Configuration
  -- If maxCols is set, restrict headers. Otherwise use all headers.
  let effectiveHeaders := match maxCols with
    | some n => headers.take n
    | none   => headers

  let numCols := effectiveHeaders.length

  -- B. Apply Row Configuration
  -- If maxRows is set, restrict rows. Otherwise use all rows.
  let limitedRows := match maxRows with
    | some n => rows.take n
    | none   => rows

  -- C. Normalize Data
  -- Ensure all rows match the column count (pad or truncate)
  let normalizedRows := limitedRows.map (fun r => normalizeRow r numCols)

  -- D. Calculate Widths (Same as before, but on normalized data)
  let allData := effectiveHeaders :: normalizedRows
  let colWidths := List.range numCols |>.map fun colIdx =>
    let colStrings := allData.filterMap (fun r => r[colIdx]?)
    let maxLen := colStrings.foldl (fun acc s => Max.max acc s.length) 0
    maxLen

  -- E. Formatting Helpers
  let formatRow (r : List String) : String :=
    let parts := r.zip colWidths |>.map (fun (txt, w) => padRight txt w)
    "| " ++ String.intercalate " | " parts ++ " |"

  let separator :=
    let parts := colWidths.map (fun w => "".pushn '-' w)
    "+-" ++ String.intercalate "-+-" parts ++ "-+"
  -- D. Print Caption (Centered)
  -- We calculate the total width of the table to center the caption nicely
  let tableWidth := separator.length
  match caption with
  | some c =>
      IO.println ""                 -- Empty line for spacing
      IO.println (center c tableWidth) -- Centered caption
      IO.println ""                 -- Empty line for spacing
  | none => pure ()
  -- F. Print
  IO.println separator
  IO.println (formatRow effectiveHeaders)
  IO.println separator
  for row in normalizedRows do
    IO.println (formatRow row)
  IO.println separator

-----------------------------------------------------------
-- -- Usage Examples
-- -----------------------------------------------------------
-- def run : IO Unit := do
--   let headers := ["ID", "Operator", "Input", "Info", "Status"]
--   let rows := [
--     ["1", "Mul", "A.dat", "Fast", "Done"],
--     ["2", "Add", "B.dat", "Slow", "Fail"],
--     ["3", "Sub", "C.dat"],  -- Note: This row is missing columns!
--     ["4", "Div", "D.dat", "Normal", "Done", "Extra"] -- Note: This has too many!
--   ]

--   IO.println "--- 1. Default (Show Everything, auto-fix ragged rows) ---"
--   printTable headers rows

--   IO.println "\n--- 2. Configured: Max 2 Rows, Max 3 Columns ---"
--   printTable headers rows (maxRows := some 2) (maxCols := some 3)

-- #eval run
