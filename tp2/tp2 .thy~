theory tp2
imports Main
begin

lemma " \<forall>(x::nat) (y::nat). x + y = y+x"
nitpick
apply auto 
done

(*TP2*)

(*Construction d'ensemble*)

(*Exercice 1*)

fun member::"nat => nat list => bool"
where
"member a [] = False"|
"member a (x#xs) = (if a=x then True else (member a xs))"

value "member 1 [2,3,4]"
value "member 1 [1,2,3]"

(* Exercice 2*)

fun isSet:: "nat list \<Rightarrow> bool"
where
"isSet [] = True"|
"isSet (a#xs) = (if (member a xs) then False else (isSet xs))"

value "isSet [1, 1, 2, 3]"
value "isSet [1, 2, 3]"

(* Exercice 3 *)

fun clean::"nat list \<Rightarrow> nat list"
where
"clean [] = []"|
"clean (x#xs) = (if (isSet (x#xs)) 
                 then (x#xs) 
                 else if (member x xs) 
                 then clean(xs)
                 else (x#(clean xs)))"

value "clean [1,1] "
value "clean [1,2,3]"

(* Exercice 4  *)

lemma "(member x l) = (member x (clean l)) "
nitpick
apply auto
done

(*Exercice 5*)

lemma "(isSet (clean [1,2,3,4,4,5])) = True"
nitpick
apply auto
done

(*Suppression d'un élément*)

(*Exercice 6*)
fun delete::"nat \<Rightarrow> nat list \<Rightarrow> nat list"
where
"delete x [] = []"|
"delete x (a#xs) = (if (x=a) then xs else (a#(delete x xs)))"

(*Exercice 7*)

lemma "(member (1::nat) (delete (1::nat) [1,2,3,4,4,5])) = False"
nitpick
apply auto
done

lemma "(member (1::nat) (delete (9::nat) [1,2,3,4,4,5])) = True"
nitpick
apply auto
done

(*Intersection*)

(*Exercice 8*)

fun intersection::"nat list \<Rightarrow> nat list \<Rightarrow> nat list"
where
"intersection [] l = []"|
"intersection l [] = []"|
"intersection (x#xs) l = (if (member x l) 
                         then x#(intersection xs l)
                         else intersection xs l)"

(*Exercice 9*)

lemma "\<forall>(x::nat). (((member x [1, 2, 3, 4]) \<and> (member x [2, 7, 9, 1])) = (member x (intersection [1, 2, 3, 4] [2, 7, 9, 1])))"
nitpick
apply auto
done

(*Exercice 10*)
lemma "\<forall>(l::nat list) (s:: nat list). isSet (intersection l s) = True"


(*Union*)

(*Exercice 11*)
fun union::"nat list \<Rightarrow> nat list \<Rightarrow> nat list"
where
"union l1 l2 = clean(l1@l2)"


(*Exercice 12*)

(*Exercice 13*)

(*Egalité*)

(*Exercice 14*)

(*Exercice 15*)

end


