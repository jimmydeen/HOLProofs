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

Theorem DIVIDES_TRANS:
  ∀a b c. a divides b ∧  b divides c ⇒ a divides c
Proof
  rw[divides_def] >> qexists_tac ‘x * x'’ >> rw[]
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

Theorem DIVIDES_ONE:
  ∀x. (x divides 1) = (x = 1)
Proof
  rw[divides_def]
QED

Theorem DIVIDES_SUB:
  ∀d a b. d divides a ∧ d divides b ⇒ d divides (a-b)
Proof
  rw [divides_def, LEFT_SUB_DISTRIB] >>
  qexists_tac ‘x-x'’ >>
  rw[]
QED

Theorem DIVIDES_ADDL:
  ∀d a b. d divides a ∧ d divides (a+b) ⇒ d divides b
Proof
  rw[divides_def] >>
  qexists_tac ‘x'- x’ >> rw[]
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
  completeInduct_on ‘n’ >>
  rw[] >>
  Cases_on ‘prime n’ >-
   (qexists_tac ‘n’ >> rw[DIVIDES_REFL]) (*instantiates goal with 'n'*)
  >> ‘∃x. x divides n ∧ x ≠ 1 ∧ x ≠ n’ by
   (gs[prime_def] >> first_assum $ irule_at $ Pos hd >> simp[]) >>
  Cases_on ‘n’ >-
   (qexists_tac ‘2’ >> rw[PRIME_2, DIVIDES_0]) >> 
   drule_then strip_assume_tac DIVIDES_LE >>
   rfs[LESS_OR_EQ] >>
   last_assum (drule_all_then strip_assume_tac) >>
  qexists_tac ‘p’ >>
  rw[] >>
  irule DIVIDES_TRANS >>
  qexists_tac ‘x’ >>
  rw[]
QED

val th = SPEC “FACT n + 1” PRIME_FACTOR;
        
Theorem EUCLID:
  ∀n. ∃p. n < p ∧ prime p
Proof
  spose_not_then strip_assume_tac >>
  mp_tac $ SPEC “FACT n + 1” PRIME_FACTOR >>
  (rw[] >-
    rw[FACT_LESS, DECIDE “∀x. x ≠ 0 ⇔ 0 < x”]) >>
   rw[GSYM IMP_DISJ_THM] >>
   last_x_assum $ qspec_then ‘p’ mp_tac >>
   rw[NOT_LESS] >> 
   drule_then strip_assume_tac PRIME_POS >>
   drule_all_then strip_assume_tac DIV_FACT >>
   strip_tac >>
   drule_all_then strip_assume_tac DIVIDES_ADDL >>
   fs[DIVIDES_ONE, NOT_PRIME_1]
QED
                  
     

