theory NaturalDeduction
  imports Main
begin

print_statement conjI

lemma conj_rule: "⟦P; Q⟧ ⟹ P ∧ (Q ∧ P)"
  apply (rule conjI)
   apply assumption
  apply (rule conjI)
   apply assumption
  apply assumption
  done


print_statement disjE

print_statement disjI2

lemma disj_swap: "P ∨ Q ⟹ Q ∨ P"
  apply (erule disjE)
   apply (rule disjI2)
  apply assumption
  apply (rule disjI1)
  apply assumption
  done

print_statement conjunct2

lemma conj_swap: "P ∧ Q ⟹ Q ∧ P"
  apply (rule conjI)
   apply (drule conjunct2)
   apply assumption
  apply (drule conjunct1)
  apply assumption
  done

lemma conj_swap2: "P ∧ Q ⟹ Q ∧ P"
  apply (rule conjI)
   apply (erule conjunct2)
   apply (erule conjunct1)
  done

lemma conj_swap3: "P ∧ Q ⟹ Q ∧ P"
  apply (rule conjI)
   apply (frule conjunct2)
   apply assumption
  apply (drule conjunct1)
  apply assumption
  done

print_statement impI
print_statement conjE
print_statement mp

lemma imp_uncurry: "P ⟶ (Q ⟶ R) ⟹  P ∧ Q ⟶ R"
  apply (rule impI)
  apply (erule conjE)
  apply (drule mp)
   apply assumption
  apply (drule mp)
   apply assumption
  apply assumption
  done


print_statement contrapos_np
lemma contra_example: "⟦¬(P⟶Q); ¬(R⟶Q)⟧ ⟹ R"
  apply (erule_tac Q = "R ⟶ Q" in contrapos_np)
  apply (intro impI)
  by (erule notE)
