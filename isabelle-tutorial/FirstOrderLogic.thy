theory FirstOrderLogic
  imports Main
begin


lemma "\<forall>x. P x \<longrightarrow> P x"
  apply (rule allI)
  by (rule impI)


end
