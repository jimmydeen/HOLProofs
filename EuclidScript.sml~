open bossLib;



Definition divides_def:
  divides a b = (∃x. b = a * x)
End

set_fixity "divides" (Infix(NONASSOC, 450));

Definition prime_def:
  prime p ⇔ p ≠ 1 ∧ ∀x. x divides p ⇒ (x=1) ∨ (x=p)
End

open arithmeticTheory;

Theorem DIVIDES_REFL:
  !x. x divides x
Proof
  metis_tac [divides_def, MULT_CLAUSES]
QED

Theorem DIVIDES_LMUL:
  !d a x. d divides a ==> d divides (x * a)
Proof
  metis_tac [divides_def, MULT_ASSOC, MULT_SYM]
QED

Theorem DIVIDES_RMUL:
  !d a x. d divides a ==> d divides (a * x)
Proof
  metis_tac [MULT_SYM, DIVIDES_LMUL]
QED

Theorem DIVIDES_0:
  ∀x. x divides 0
Proof
  metis_tac [divides_def, MULT_CLAUSES]
QED


Theorem DIV_FACT:
  !m n. 0 < m /\ m <= n ==> m divides (FACT n)
Proof
  Induct_on ‘n - m’ >>
  rw[] >-
   (‘m = n’ by rw[] >>
    rw[] >>
    ‘∃k. m = SUC k’ by (Cases_on ‘m’ >> fs[]) >>
    fs[FACT, DIVIDES_LMUL, DIVIDES_REFL]) >>
  ‘0 < n’ by rw[] >>
  ‘∃k. n = SUC k’ by (Cases_on ‘n’ >> fs[])>>
   rw [FACT, DIVIDES_RMUL]
QED

Theorem DIVIDES_ZERO:
  ∀x. (0 divides x) = (x = 0)
Proof
  metis_tac [divides_def, MULT_CLAUSES]
QED
        
Theorem DIVIDES_LE:
  ∀m n. m divides n ⇒ m ≤ n ∨ (n = 0)
Proof
  rw [divides_def] >> rw[]
QED
        
Theorem NOT_PRIME_0:
  ~prime 0
Proof
  rw [prime_def, DIVIDES_0]
QED

Theorem NOT_PRIME_1:
  ~prime 1
Proof
  rw [prime_def]
QED

Theorem PRIME_2:
  prime 2
Proof
  rw [prime_def] >>
  metis_tac [DIVIDES_LE, DIVIDES_ZERO, DECIDE “2≠0”,
             DECIDE “x ≤ 2 ⇔ (x=0) ∨ (x=1) ∨ (x=2)”]
QED

Theorem PRIME_POS:
  ∀p. prime p ⇒ 0 < p
Proof
  Cases >> rw [NOT_PRIME_0]
QED

Theorem PRIME_FACTOR:
  ∀n. n ≠ 1 ⇒ ∃p. prime p ∧ p divides n
Proof
  completeInduct_on ‘n’




val _ = new_theory "test";

Theorem bla:
  1 + 1 = 2
Proof
  rw[]
QED


        
Definition my_append_def:
  my_append [] xs = xs ∧
  my_append (x::xs) ys = x::my_append xs ys
End

Theorem my_append_thm:
  ∀xs. my_append xs [] = xs
Proof
  Induct_on ‘xs’
  >- rw[my_append_def] >>
  rw[my_append_def]
QED

Theorem my_append_thm:
  ∀xs. my_append xs [] = xs
Proof
  Induct_on ‘xs’ >>
  rw[my_append_def]

  rw[]
QED

(*
   >>   \\  THEN

   tac1 >> tac2

   apply tac1 to the goal state,
    then apply tac2 to all subgoals produced by tac1


   >-  THEN1

   tac1 >- tac2

   apply tac1 to the goal state,
    then apply tac2 to the *first* subgoal produced by tac1,
    fail if tac2 doesn't prove this goal

 *)

val _ = export_theory();
