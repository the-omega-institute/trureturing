module
public import Init.Classical
public import OmegaInit.Core

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Classical.indefiniteDescription.match_1 Classical.propDecidable.match_1 Classical.typeDecidable.match_1)
end Omega
namespace Omega.Classical
export _root_.Classical (exists_true_of_nonempty)
end Omega.Classical
