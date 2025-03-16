--chapter 2 exercises

-- exercise 1
-- divisors of n that are stricly less than n

/--
create a list of numbers from 1 to n-1
then filter the list to keep only the numbers x
for which the remained of n/x is 0,
i.e. the numbers x that are divisors of n
-/
def divisors ( n : Nat) : List Nat :=
  List.filter (fun x => (n % x = 0)) (List.range' 1 (n-1))

#eval divisors 10
#eval divisors 0


---------------------------------------------------------------------
-- exercise 2
-- find perfect numbers < 1000

/--
a number n is perfect if
the sum of its divisors strictly less than n is equal to n
-/
def is_perfect (n : Nat) : Bool :=
  match n with
  | 0 | 1 => false
  | _ => (divisors n).sum = n

/--
create a list of numbers from 0 to n-1
then filter the list to keep only the numbers x
for which x is perfect
-/
def perfect_numbers (n : Nat) : List Nat :=
  (List.range n).filter (fun x => (is_perfect x))


--test the functions above
#eval is_perfect 0
#eval is_perfect 1
#eval is_perfect 2
#eval is_perfect 6
#eval divisors 6


-- find the list of perfect numbers < 1000
#eval perfect_numbers 1000


---------------------------------------------------------------------
-- exercise 3
/--
function that, for every list L,
returns the list of exactly all the sublists of L
-/
def find_sublists {α : Type} (xs : List α) : List (List α) :=
  match xs with
  -- the empty list has one sublist, the empty list
  | [] => [[]]
  -- if the list is not empty,
  -- find the sublists of the tail of the list
  -- then concatenate the result with the result of mapping the sublists of the tail
  -- by adding the head to each sublist
  | y :: ys => (find_sublists ys) ++ (find_sublists ys).map (fun x => y :: x)

#eval find_sublists [1, 2, 3]


---------------------------------------------------------------------
-- exercise 4
theorem length_list_of_sublists {α : Type} (xs : List α) :
  (find_sublists xs).length = 2^(xs.length) := by
  induction xs with
  | nil =>
    simp [find_sublists]
  | cons y ys ih =>
    simp [find_sublists, List.length_append, List.length_map, Nat.pow_succ, ih]
    ; linarith

-- import Mathlib?
-- import Mathlib.Tactic.Linarith


#check List.length_append
#check List.length_map
#check Nat.pow_succ
-- #check linarith

---------------------------------------------------------------------
-- exercise 5
-- permutations of a list

def insert_everywhere {α : Type} (x : α) : List α → List (List α)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insert_everywhere x ys).map (fun zs => y :: zs)

#eval insert_everywhere 3 [1, 2]


def list_permutations {α : Type} : List α → List (List α)
  | [] => [[]]
  | y :: ys => ((list_permutations ys).map (fun zs => insert_everywhere y zs)).flatten

#eval list_permutations [1, 2, 3]


---------------------------------------------------------------------
-- exercise 6

def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | (n+1) => (n+1) * factorial n

#eval factorial 0
#eval factorial 1
#eval factorial 2
#eval factorial 3

theorem t {α : Type} (xs : List α) :
  (list_permutations xs).length = factorial xs.length := by
  induction xs with
  | nil =>
    simp [list_permutations, factorial]
  | cons y ys ih =>
    simp [list_permutations, List.length, factorial, List.length_map, List.length_flatten, ih]
    ; linarith

---------------------------------------------------------------------
-- exercise 7

-- check if all the sublists of a list have the same length
def check_equal_length {α : Type} (xs : List (List α)) : Bool :=
  match xs with
  | [] => true
  | y :: ys => ys.all (fun zs => y.length = zs.length)

#eval check_equal_length [[1, 2], [3, 4], [5, 6]]
#eval check_equal_length [[1, 2], [3, 4], [5, 6, 7]]

--
def transpose {α : Type} (M : List (List α)) : List (List α) :=
  match M with
  | []         => [] -- no rows → empty matrix
  | [] :: _    => [] -- first row is empty → no columns → empty matrix
  | _          =>
    let heads := M.map (fun row => row.head!)
    let tails := M.map (fun row => row.tail!)
    heads :: transpose tails
-- termination_by
--   List.foldl (fun acc row => acc + row.length) 0 M

#eval transpose [[1, 2], [3, 4], [5, 6]]
