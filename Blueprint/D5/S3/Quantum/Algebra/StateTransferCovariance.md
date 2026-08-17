# Finite-State Read Covariance

## Abstract

Pointwise reads intertwine finite-state pushforwards with pulled-back observables.

**Theorem 1.1 (Pointwise reads intertwine finite-state pushforwards).**

$$\forall Y \operatorname{finite}, \tau: Y \to Y, f: Y \to \mathbb{C},\ \alpha_{\tau}(f) = f \circ \tau,\quad M_{f} \circ L_{\tau} = L_{\tau} \circ M_{\alpha_{\tau}(f)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateTransferCovariance.diagonal_state_transfer_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y be a finite state type, let tau be any self-map of Y, and let f be a complex-valued observable. Write L_tau for the canonical finite pushforward and M_f for pointwise multiplication by f. Then M_f after L_tau equals L_tau after multiplication by the pulled-back observable f after tau.

The Lean declaration uses the existing readObservable operator and mathlib's FunOnFinite.map without redefining either construction. It applies FunOnFinite.map_apply_apply to expose the fiber sum and Finset.mul_sum to distribute the read value; equality on each fiber identifies f(tau(y)) with f(z).

Loogle and LeanSearch found the pushforward and its fiber-sum theorem, but no full covariance result. Repository and digestion-record searches likewise found no duplicate. The theorem allows arbitrary finite self-maps and does not assume reversibility.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/StateTransferCovariance.diagonal_state_transfer_covariance`
