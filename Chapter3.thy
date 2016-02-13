theory Chapter3
imports Main
begin

type_synonym data_object = string
type_synonym method_name = string
type_synonym thread = nat

datatype history_element = Invocation data_object method_name thread 
                           | Response data_object method_name thread

fun get_task :: "history_element \<Rightarrow> nat" where
"get_task (Invocation d m t) = t" |
"get_task (Response d m t) = t" 

fun get_object :: "history_element \<Rightarrow> data_object" where
"get_object (Invocation d m t) = d" |
"get_object (Response d m t) = d" 

type_synonym history = "history_element list"

fun is_in :: "history \<Rightarrow> history_element \<Rightarrow> bool" where
"is_in [] e = False" |
"is_in (head#tail) e = (if (head = e) then True else (is_in tail e))"  

fun history_before :: "history \<Rightarrow> history_element \<Rightarrow> history" where
"history_before [] e = []" |
"history_before (head#tail) e = (if (head = e) then [] else [head]@(history_before tail e))" 

fun history_after :: "history \<Rightarrow> history_element \<Rightarrow> history" where
"history_after [] e = []" |
"history_after (head#tail) e = (if (head = e) then tail else (history_after tail e))" 

fun precedes :: "history \<Rightarrow> history_element \<Rightarrow> history_element \<Rightarrow> bool" where
"precedes [] _ _ = False" |
"precedes (head#tail) e1 e2 = (if (head = e1) then True else (if (head = e2) then False else (precedes tail e1 e2)))" 

value "[(Invocation ''a'' ''m'' 1)]"

fun matches :: "history_element \<Rightarrow> history_element \<Rightarrow> bool" where
"matches (Invocation d1 m1 t1) (Response d2 m2 t2) = ((d1 = d2) \<and> (m1 = m2) \<and> (t1 = t2))" |
"matches _ _ = False"

fun is_invocation :: "history_element \<Rightarrow> bool" where
"is_invocation (Invocation _ _ _) = True" |
"is_invocation _ = False"

fun has_response :: "history_element \<Rightarrow> history \<Rightarrow> bool" where
"has_response _ [] = False" |
"has_response e (head#tail) = (if (matches e head) then True else (has_response e tail))" 

fun get_response :: "history_element \<Rightarrow> history \<Rightarrow> history_element option" where
"get_response _ [] = None" |
"get_response e (head#tail) = (if (matches e head) then (Some e) else (get_response e tail))" 

fun is_sequential :: "history \<Rightarrow> bool" where
"is_sequential [] = True" |
"is_sequential [(Invocation _ _ _)] = True" |
"is_sequential [(Response _ _ _)] = False" |
"is_sequential (h1#tail1) 
 = (case tail1 of
      h2#[] \<Rightarrow> (matches h1 h2)
    | (h2#tail2)            \<Rightarrow> if (matches h1 h2) then (is_sequential tail2) else False)" 

value "(is_sequential 
[
 (history_element.Invocation ''a'' ''m1'' 2),
 (history_element.Response   ''a'' ''m1'' 2)
])"

value "(is_sequential 
[
 (history_element.Invocation ''a'' ''m1'' 2),
 (history_element.Response   ''a'' ''m1'' 2),
 (history_element.Invocation ''a'' ''m1'' 2),
 (history_element.Response   ''b'' ''m1'' 2)
])"

value "(is_sequential 
[
 (history_element.Invocation ''a'' ''m1'' 1),
 (history_element.Response   ''a'' ''m1'' 1),
 (history_element.Invocation ''a'' ''m2'' 3),
 (history_element.Response   ''a'' ''m2'' 3)
])"

fun thread_subhistory :: "history \<Rightarrow> thread \<Rightarrow> history" where
"thread_subhistory (h1#tail) t = 
  (if ((get_task h1) = t) then h1#(thread_subhistory tail t) else (thread_subhistory tail t))" |
"thread_subhistory [] t = []"

value "(thread_subhistory 
[
 (history_element.Invocation ''a'' ''m1'' 1),
 (history_element.Response   ''a'' ''m1'' 1),
 (history_element.Invocation ''a'' ''m2'' 3),
 (history_element.Response   ''a'' ''m2'' 3)
]
3
)"

definition at_most_once_found :: "history \<Rightarrow> history_element \<Rightarrow> bool" where
"at_most_once_found h e = ((is_in h e) \<longrightarrow> \<not>(is_in (history_after h e) e))"

definition is_well_formed :: "history \<Rightarrow> bool" where
"is_well_formed h = ((\<forall>i.(is_sequential (thread_subhistory h i))) \<and> (\<forall>e.(at_most_once_found h e)))"

definition are_equivalent :: "history \<Rightarrow> history \<Rightarrow> bool" where
"are_equivalent h1 h2 = (\<forall>i.(thread_subhistory h1 i) = (thread_subhistory h2 i))" 

(* Lemmas for sanity check *)

lemma "(is_well_formed [])"
apply(simp add:is_well_formed_def add:at_most_once_found_def)
done

lemma "h1 = h2 \<longrightarrow> (are_equivalent h1 h2)"
apply(simp add:are_equivalent_def add:at_most_once_found_def)
done

fun only_responses :: "history \<Rightarrow> bool" where
"only_responses [] = True" |
"only_responses ((Response _ _ _)#tail) = (only_responses tail)" |
"only_responses _ = False" 

(* common prefix, then only responses, and a legal history: *)
definition is_extension :: "history \<Rightarrow> history \<Rightarrow> bool" where
"is_extension h1 h2 = ((is_well_formed h1) 
                        \<and> (is_well_formed h2) 
                        \<and> (\<exists>suffix.((h2 = h1@suffix) \<and> only_responses(suffix))))" 

lemma "is_extension [(Invocation d m t)] [(Invocation d m t), (Response d m t)]"
apply(simp add:is_extension_def)
apply(simp add:is_well_formed_def)
apply(auto)
apply(simp add:at_most_once_found_def)
apply(simp add:at_most_once_found_def)
apply(auto)
done

fun complete :: "history \<Rightarrow> history" where
"complete [] = []" |
"complete ((Response d m t)#tail) = (Response d m t)#(complete tail)" |
"complete ((Invocation d m t)#tail) = (if (has_response (Invocation d m t) tail) 
                                     then (Invocation d m t)#(complete tail) 
                                     else (complete tail))" 

value "(complete [(Invocation ''a'' ''b'' 1), (Invocation ''a'' ''b'' 2), (Response ''a'' ''b'' 1)])"

fun method_call_precedes :: "history \<Rightarrow> history_element \<Rightarrow> history_element \<Rightarrow> bool" where
"method_call_precedes h (Invocation d1 m1 t1) (Invocation d2 m2 t2) = 
  (if (\<not>((is_in h (Invocation d1 m1 t1) \<and> (is_in h (Response d1 m1 t1)) \<and> (is_in h (Invocation d2 m2 t2))))) 
     then False
   else
     (precedes h (Response d1 m1 t1) (Invocation d2 m2 t2)))" |
"method_call_precedes h _ _  = False"

lemma "(\<not>(is_in h (Invocation d1 m1 t1)) \<and> (is_well_formed h))
        \<longrightarrow> \<not>(method_call_precedes h (Invocation d1 m1 t1) (Invocation d2 m2 t2))"
apply(auto)
done

lemma "(\<not>(is_in h (Invocation d1 m1 t1)) \<and> (is_well_formed h))
        \<longrightarrow> \<not>(method_call_precedes h (Invocation d1 m1 t1) (Invocation d2 m2 t2))"
apply(auto)
done

definition is_linearizable :: "history \<Rightarrow> bool" where
"is_linearizable H = 
  (\<exists>extension.((is_extension extension H)
              \<and> (is_well_formed extension)
              \<and> (\<exists>S.((is_sequential S)
                      \<and> (is_well_formed S)
                      \<and> (are_equivalent (complete extension) S)) (* L1 *)
                      \<and> (\<forall>m0.(\<forall>m1.(method_call_precedes H m0 m1) 
                                   \<longrightarrow> (method_call_precedes S m0 m1))) (*L2*)
)))"

fun object_subhistory :: "history \<Rightarrow> data_object \<Rightarrow> history" where
"object_subhistory (h1#tail) object = 
  (if ((get_object h1) = object) then h1#(object_subhistory tail object) else (object_subhistory tail object))" |
"object_subhistory [] t = []"

lemma "linearizability_is_compositional" : 
    "(is_well_formed H) \<longrightarrow> 
       ((\<forall>object.(is_linearizable (object_subhistory H object))) \<longrightarrow> (is_linearizable H))"
apply(auto)
apply(simp add:is_linearizable_def add:is_well_formed_def add:is_extension_def add:is_sequential_def add:at_most_once_found_def)
apply(auto)
apply(rule exI)
apply(auto)
apply(rule exI)
apply(rule mp)
apply(auto)
apply(rule allE)
apply(auto)
(* tbc *)