theory IsZero
  imports Main
begin

text \<open>Proof that the IsZero template is correct, assuming the signals are values of some arbitrary field\<close>

definition is_zero :: "'a::field \<Rightarrow> 'a::field" where
  "is_zero in_sig \<equiv> if in_sig = 0 then 1 else 0"

text \<open>First we show that, if the constraints are satisfied, then the output signal is correct.\<close>

lemma l1:
  fixes in_sig inv_sig out_sig :: "'a::field"
  defines "out_sig \<equiv> (-in_sig)*inv_sig + 1"
  assumes "in_sig*out_sig = 0"
  shows "out_sig = is_zero in_sig"
    \<comment> \<open>note that @{term inv_sig} is left unconstrained\<close>
  by (metis add_0 assms(1,2) is_zero_def mult_eq_0_iff mult_minus_left)

text \<open>Next we show that the expression assigned to the inv signal satisfies the constraints\<close>

lemma l2:
  fixes in_sig inv_sig out_sig :: "'a::field"
  defines "inv_sig \<equiv> (if in_sig \<noteq> 0 then (1/in_sig) else 0)"
  and "out_sig \<equiv> (-in_sig)*inv_sig + 1"
shows "in_sig*out_sig = 0"
  by (simp add: inv_sig_def out_sig_def)

end