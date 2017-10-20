theory Defs
imports Main
begin


lemma falseE: "\<lbrakk> A; ~A\<rbrakk> \<Longrightarrow> False"
by auto

lemma falseI: "False \<Longrightarrow> P"
by auto

(* Trick to have simple command names: no distinction between rule (rtac) et drule (etac) *)

method_setup conjE2 = {* Scan.succeed
      (K (SIMPLE_METHOD ((dtac @{thm conjunct2} 1)))) *}

method_setup conjE1 = {* Scan.succeed
      (K (SIMPLE_METHOD ((dtac @{thm conjunct1} 1)))) *}

method_setup conjI = {* Scan.succeed
      (K (SIMPLE_METHOD ((rtac @{thm conjI} 1)))) *}

method_setup impI = {* Scan.succeed
      (K (SIMPLE_METHOD ((rtac @{thm impI} 1)))) *}

method_setup impE = {* Scan.succeed
      (K (SIMPLE_METHOD ((dtac @{thm mp} 1)))) *}

method_setup disjI1 = {* Scan.succeed
      (K (SIMPLE_METHOD ((rtac @{thm disjI1} 1)))) *}

method_setup disjI2 = {* Scan.succeed
      (K (SIMPLE_METHOD ((rtac @{thm disjI2} 1)))) *}

method_setup disjE = {* Scan.succeed
      (K (SIMPLE_METHOD ((etac @{thm disjE} 1)))) *}

method_setup notE = {* Scan.succeed
      (K (SIMPLE_METHOD ((etac @{thm notE} 1)))) *}

method_setup notI = {* Scan.succeed
      (K (SIMPLE_METHOD ((rtac @{thm notI} 1)))) *}

method_setup allI = {* Scan.succeed
      (K (SIMPLE_METHOD ((rtac @{thm allI} 1)))) *}

method_setup allE = {* Scan.succeed
      (K (SIMPLE_METHOD ((dtac @{thm spec} 1)))) *}

method_setup exI = {* Scan.succeed
      (K (SIMPLE_METHOD ((rtac @{thm exI} 1)))) *}

method_setup exE = {* Scan.succeed
      (K (SIMPLE_METHOD ((etac @{thm exE} 1)))) *}

method_setup falseE = {* Scan.succeed
      (K (SIMPLE_METHOD ((rtac @{thm falseE} 1)))) *}

method_setup falseI = {* Scan.succeed
      (K (SIMPLE_METHOD ((rtac @{thm falseI} 1)))) *}

end