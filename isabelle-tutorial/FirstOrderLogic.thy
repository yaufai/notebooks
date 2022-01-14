theory FirstOrderLogic
  imports Main
begin


lemma "\<forall>x. P x \<longrightarrow> P x"
  apply (rule allI)
  by (rule impI)

print_statement impI
(* [ P \<Longrightarrow> Q ] \<Longrightarrow>  (P \<longrightarrow> Q) *)

print_statement allI
(* [ \<And>x. P x ] \<Longrightarrow> \<forall>x. P x *)

print_statement spec
(* [ \<forall>x. P x ] \<Longrightarrow> P x *)


lemma "(\<forall>x. P \<longrightarrow> Q x) \<Longrightarrow> P \<longrightarrow> (\<forall>x. Q x)"
  (* [ \<forall>x. P \<longrightarrow> Q x ] \<Longrightarrow> P \<longrightarrow> \<forall>x. Q x *)
  apply (rule impI)
  (* [ \<forall>x. P \<longrightarrow> Q x; P ] \<Longrightarrow> \<forall>x. Q x *)
  apply (rule allI)
  (*  \<And>x. [ \<forall>x. P \<longrightarrow> Q x; P ] \<Longrightarrow> Q x *)
  (*
  
  *)

end
