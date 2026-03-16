-- 1. Helper: Escape string for CSV format
-- Rules:
-- - If it contains a comma, newline, or double quote, wrap the whole thing in double quotes.
-- - Existing double quotes must be escaped by doubling them (" -> "").
def escapeCSV (s : String) : String :=
  let needsQuotes := s.any (fun c => c == ',' || c == '\n' || c == '\"')
  if needsQuotes then
    let escaped := s.replace "\"" "\"\""
    s!"\"{escaped}\""
  else
    s

-- 2. Helper: Convert a list of rows to a single CSV string
def toCSVString (headers : List String) (rows : List (List String)) : String :=
  let formatRow (r : List String) :=
    (r.map escapeCSV) |> String.intercalate ","

  let headerStr := formatRow headers
  let rowsStr := rows.map formatRow |> String.intercalate "\n"

  if rows.isEmpty then headerStr
  else headerStr ++ "\n" ++ rowsStr

-- 3. Main IO Function: Save to file
def saveCSV (filename : String) (headers : List String) (rows : List (List String)) : IO Unit := do
  let content := toCSVString headers rows
  IO.FS.writeFile filename content
  IO.println s!"Successfully saved CSV to: {filename}"
