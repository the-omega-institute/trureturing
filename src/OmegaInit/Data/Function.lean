module
public import Init.Data.Function
public import OmegaInit.Core

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Function.HasLeftInverse.injective Function.HasRightInverse.surjective Function.Injective.comp Function.Injective.eq_iff Function.Injective.eq_iff' Function.Injective.ne Function.Injective.ne_iff Function.Injective.ne_iff' Function.LeftInverse.eq_1 Function.LeftInverse.injective Function.RightInverse.eq_1 Function.RightInverse.surjective Function.Surjective.comp)
end Omega
namespace Omega.Function
export _root_.Function (HasLeftInverse HasRightInverse Injective LeftInverse RightInverse Surjective curry injective_id leftInverse_of_surjective_of_rightInverse rightInverse_of_injective_of_leftInverse surjective_id uncurry)
end Omega.Function
