import Autoinc.Change

/--
Used for testing operators
-/
def testOp [Monad m] [BEq β]
  [Change α Δα]
  [Change β Δβ]
  (f : α → m β) (Δf : Δα → m Δβ) (a : α) (da : Δα) := do
  pure ((←f a) ⨁ (←Δf da) == (← f (a ⨁ da)))


def medianOfSorted (arr : Array Float) : Float :=
  let n := arr.size
  if n == 0 then
    panic! "medianOfSorted: empty array"
  else if n % 2 == 1 then
    arr[n / 2]!
  else
    let mid1 := arr[n / 2 - 1]!
    let mid2 := arr[n / 2]!
    (mid1 + mid2) / 2.0

def filterIqr15 (xs : List Float) : List Float :=
  let n := xs.length
  if n < 4 then
    xs
  else
    let sorted := xs.toArray.qsort (· < ·)
    let lower := sorted.extract 0 (n / 2)
    let upper := sorted.extract ((n + 1) / 2) n
    let q1 := medianOfSorted lower
    let q3 := medianOfSorted upper
    let iqr := q3 - q1
    let loBnd := q1 - 1.5 * iqr
    let hiBnd := q3 + 1.5 * iqr
    xs.filter (fun x => x >= loBnd && x <= hiBnd)

/-- Helper: Calculate the average (mean) of a list of floats -/
def mean (xs : List Float) : Float :=
  if xs.isEmpty then 0.0
  else
    let sum := xs.foldl (· + ·) 0.0
    sum / xs.length.toFloat

/-- Calculate the Standard Deviation (Population) -/
def stdDev (xs : List Float) : Float :=
  let n := xs.length.toFloat
  if n == 0.0 then 0.0
  else
    let m := mean xs
    -- Calculate variance: sum((x - mean)^2) / n
    let sumSqDiff := xs.foldl (fun acc x => acc + (x - m) ^ 2.0) 0.0
    let variance := sumSqDiff / n
    Float.sqrt variance

/- Round up a float -/
partial def Float.trunc (f : Float) (prec : Nat := 3) : String :=
  -- 1. Handle Sign
  if f < 0 then
    "-" ++ Float.trunc (-f) prec
  else
    -- 2. Shift the decimal point (e.g., 1.2345 -> 1234.5)
    let factor := (10.0 ^ (Float.ofNat prec))
    let shifted := f * factor

    -- 3. Round to nearest integer (e.g., 1234.5 -> 1235.0)
    -- We use toUInt64 for conversion, assuming the number fits in 64 bits.
    let val := shifted.round.toUInt64.toNat
    let s := ToString.toString val

    -- 4. Pad with leading zeros if necessary (e.g., 0.012 -> "12" -> "0012")
    let padded :=
      if s.length <= prec then
        "".pushn '0' (prec + 1 - s.length) ++ s
      else
        s

    -- 5. Insert the decimal point
    let splitIdx := padded.length - prec
    let intPart := padded.take splitIdx
    let fracPart := padded.drop splitIdx
    s!"{intPart}.{fracPart}"


-- def main : IO Unit := do
--   let data := [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0]
--   let dataWithOutliers := [-50.0] ++ data ++ [100.0]

--   let result := filterIqr15 dataWithOutliers

--   IO.println s!"original: {dataWithOutliers}"
--   IO.println s!"filtered: {result}"
