-- exercise 1
def divisors (n : Nat) : List Nat :=
  List.filter (fun x => (¬ (x = 0)) ∧ (n % x = 0)) (List.range (n+1))

#eval divisors 10
#eval divisors 0

-- exercise 2
