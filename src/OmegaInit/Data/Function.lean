module
public import Init.Data.Function
public import OmegaInit.Core

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Function
export _root_.Function (Injective LeftInverse RightInverse Surjective)
end Omega.Function
namespace Omega.Function.LeftInverse
export _root_.Function.LeftInverse (injective)
end Omega.Function.LeftInverse
namespace Omega.Function.RightInverse
export _root_.Function.RightInverse (surjective)
end Omega.Function.RightInverse
