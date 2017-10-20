theory tp1bis
imports Main Defs
begin 


(* Defs defines sequent calculus deduction rules.
   By importing this theory, you will have access to:
   - assumption
   - impI, impE (introduction/elimination of implications)
   - conjI, conjE1, conjE2 (same for conjunctions)
   - disjI1, disjI2, disjE (same for disjunctions)
   - notI/notE (same for not)
   - allI/allE (same for \<forall>)
   - exI/exE (same for \<exists>)
   - falseI/falseE (same for False)
*) 

(* Here is an example of use of those rules *)
lemma "A \<longrightarrow> (B \<longrightarrow> A)"
apply impI
apply impI
apply assumption
done


lemma "(P \<longrightarrow> (Q \<longrightarrow> R)) \<longrightarrow> (P \<and> Q \<longrightarrow> R)"

lemma "~(A \<longrightarrow> A) \<longrightarrow> B"


lemma "B \<longrightarrow> ~(~(A \<longrightarrow> A))"


lemma "A \<or> B \<longrightarrow> B \<or> A"

lemma "A \<and> B \<longrightarrow> B \<and> A"


lemma "(\<forall> x. P(x)) \<longrightarrow> (\<exists> x. P(x))"

end