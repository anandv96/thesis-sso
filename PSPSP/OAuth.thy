(*

Title:      OAuth.thy 
SPDX-License-Identifier: BSD-3-Clause
*)
section\<open>OAuth\<close>

text\<open>we stole this from ...\<close>

theory OAuth
  imports "Automated_Stateful_Protocol_Verification.PSPSP"
begin

declare [[pspsp_timing]]

trac_import "OAuth.trac"


subsection \<open>Protocol model setup\<close>
protocol_model_setup spm: OAuth

subsection \<open>(G)SMP computations\<close>
compute_SMP [optimized] OAuth_protocol_sso_with_star_projs ssowithstar_SMP
compute_SMP [optimized] OAuth_protocol_tls_with_star_projs tlswithstar_SMP
compute_SMP [GSMP] OAuth_protocol_sso_with_star_projs ssowithstar_GSMP
compute_SMP [GSMP] OAuth_protocol_tls_with_star_projs tlswithstar_GSMP
compute_SMP [composition_optimized] OAuth_protocol OAuth_SMP

subsection \<open>Proof of security of the component protocols\<close>
compute_fixpoint OAuth_protocol_sso_with_star_projs sso_fixpoint
compute_fixpoint OAuth_protocol_tls_with_star_projs tls_fixpoint

value "let (FP,OCC,TI) = sso_fixpoint in (size FP, size OCC, size TI)"
value "let (FP,OCC,TI) = tls_fixpoint in (size FP, size OCC, size TI)"

protocol_security_proof [unsafe] sso_ssp: OAuth
  for OAuth_protocol_sso_with_star_projs sso_fixpoint ssowithstar_SMP
    \<comment> \<open>Is the fixed point free of attack signals?\<close>
value "attack_notin_fixpoint sso_fixpoint"

value "sso_fixpoint"

\<comment> \<open>Is the protocol covered by the fixed point?\<close>
value "protocol_covered_by_fixpoint sso_fixpoint OAuth_protocol_sso_with_star_projs"

\<comment> \<open>Is the fixed point analyzed?\<close>
value "analyzed_fixpoint sso_fixpoint"

\<comment> \<open>Is the protocol well-formed?\<close>
value "wellformed_protocol' OAuth_protocol_sso_with_star_projs ssowithstar_SMP"

\<comment> \<open>Is the fixed point well-formed?\<close>
value "wellformed_fixpoint sso_fixpoint"

protocol_security_proof [unsafe] tls_ssp: OAuth
  for OAuth_protocol_tls_with_star_projs tls_fixpoint tlswithstar_SMP
    \<comment> \<open>Is the fixed point free of attack signals?\<close>
value "attack_notin_fixpoint tls_fixpoint"

\<comment> \<open>Is the protocol covered by the fixed point?\<close>
value "protocol_covered_by_fixpoint tls_fixpoint OAuth_protocol_tls_with_star_projs"

\<comment> \<open>Is the fixed point analyzed?\<close>
value "analyzed_fixpoint tls_fixpoint"

\<comment> \<open>Is the protocol well-formed?\<close>
value "wellformed_protocol' OAuth_protocol_tls_with_star_projs tlswithstar_SMP"

\<comment> \<open>Is the fixed point well-formed?\<close>
value "wellformed_fixpoint tls_fixpoint"


subsection \<open>Compositionality\<close>
compute_shared_secrets tlswithstar_GSMP ssowithstar_GSMP OAuth_Sec

thm OAuth_Sec_def

protocol_composition_proof [unsafe] OAuth_comp: OAuth
  for OAuth_protocol OAuth_SMP OAuth_Sec
  and OAuth_protocol_tls OAuth_protocol_sso
  and OAuth_protocol_tls_with_star_projs OAuth_protocol_sso_with_star_projs
  and tlswithstar_GSMP ssowithstar_GSMP

lemma OAuth_comp_secure:
  assumes wt_leakage_free:
    "spm.welltyped_leakage_free_protocol OAuth_Sec OAuth_protocol_sso_with_star_projs"
    "spm.welltyped_leakage_free_protocol OAuth_Sec OAuth_protocol_tls_with_star_projs"
  shows
    "\<forall>\<A> \<in> spm.reachable_constraints OAuth_protocol. \<nexists>\<I>.
      spm.constraint_model \<I> (\<A>@[\<langle>0, send\<langle>[attack\<langle>ln 0\<rangle>]\<rangle>\<rangle>])"
    "\<forall>\<A> \<in> spm.reachable_constraints OAuth_protocol. \<nexists>\<I>.
      spm.constraint_model \<I> (\<A>@[\<langle>1, send\<langle>[attack\<langle>ln 1\<rangle>]\<rangle>\<rangle>])"
using wt_leakage_free
      OAuth_comp.composed_protocol_preserves_component_goals
      sso_ssp.protocol_welltyped_secure
      tls_ssp.protocol_welltyped_secure
by auto

end
