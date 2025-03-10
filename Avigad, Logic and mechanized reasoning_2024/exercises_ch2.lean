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
