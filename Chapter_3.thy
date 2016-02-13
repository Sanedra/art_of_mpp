theory Chapter_3
imports Main
begin

type_synonym data_object = string
type_synonym method_name = string
type_synonym thread = nat



datatype history_element = Invocation data_object method_name thread 
                           | Response data_object method_name thread
                           | Empty
type_synonym history = "nat \<Rightarrow> history_element"

fun matches :: "history_element \<Rightarrow> history_element \<Rightarrow> bool" where
"matches (Invocation d1 m1 t1) (Response d2 m2 t2) = ((d1 = d2) \<and> (t1 = t2))" |
"matches _ _ = False"

(* TODO: syntax *)
definition is_finite_history :: "history \<Rightarrow> bool" where
"is_finite_history h = (\<exists>i. (\<forall>j>i.((h i) = Empty)))"

fun is_invocation :: "history_element \<Rightarrow> bool" where
"is_invocation (Invocation _ _ _) = True" |
"is_invocation _ = False"

definition is_response :: "history \<Rightarrow> nat \<Rightarrow> bool" where
"is_response h x = (\<exists>i<x.(matches (h i) (h x)))"

definition has_response :: "history \<Rightarrow> nat \<Rightarrow> bool" where
"has_response h x = (\<exists>i>x.(matches (h x) (h i)))"

definition form_method_call :: "history \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"form_method_call h i1 i2 = ((i1 < i2) \<and> (matches (h i1) (h i2)) 
                             \<and> \<not>(\<exists>m>i1.(m<i2 \<and> (matches (h i1) (h m)))))"

definition is_sequential :: "history \<Rightarrow> bool" where
"is_sequential h = (\<forall>i.(matches (h (2*i)) (h (2*i+1))))"

definition is_extension :: "history \<Rightarrow> history \<Rightarrow> bool" where
"is_extension h1 h2 = (\<exists>i.((\<forall>j\<le>i.(((h1 i) = (h2 j))))
                          \<and>(\<forall>j>i.(\<exists>k\<le>i.(form_method_call h2 k i)))))"

definition is_closed :: "history \<Rightarrow> bool" where
"is_closed h = (\<forall>i.((is_invocation (h i)) \<longrightarrow> (has_response h i)))"

fun get_task :: "history_element \<Rightarrow> nat" where
"get_task (Invocation d m t) = t" |
"get_task (Response d m t) = t" |
"get_task Empty = 0"

fun thread_subhistory :: "history \<Rightarrow> thread \<Rightarrow> history" where
"thread_subhistory h t = (\<lambda>x.(if ((get_task (h x)) = t) then (h x) else Empty))"


definition empty_history ("<>") where
  "empty_history \<equiv> \<lambda>x. Empty"

fun update :: "history \<Rightarrow> nat \<Rightarrow> history_element \<Rightarrow> history" where
"update h i e  = (\<lambda>x.(if (x = i) then e else (h x)))"

value "(Invocation ''a'' ''b'' 1)"

value "((thread_subhistory (update empty_history 0 (history_element.Invocation ''O1'' ''m1'' 1)) 2) 0)"

definition is_valid_history :: "history \<Rightarrow> bool" where
"is_valid_history h = (\<forall>thread.(is_sequential (thread_subhistory h thread)))"



fun has_response :: "data_object \<Rightarrow> method_name \<Rightarrow> thr
H_1 = P_1
H_2 = P_2 S_2

P_1 == P_2
only responses in S_2

*)

