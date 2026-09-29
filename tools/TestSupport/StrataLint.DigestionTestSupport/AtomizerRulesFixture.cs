namespace StrataLint.TestSupport;

internal static class AtomizerRulesFixture
{
    internal static readonly string FirstScheme = string.Concat("gi", "ct");
    internal static readonly string SecondScheme = string.Concat("pz", "g");

    internal static string Minimal => """
        schema_version = 1

        [[observer.claim_prefixes]]
        prefix = "**Known**"
        locator = "theorem/known"

        [[cone.claim_prefixes]]
        prefix = "定理"
        locator = "theorem/{number}|theorem-form/{number}"

        [[first.genres]]
        token = "定理"
        kind = "theorem"

        [[first.claim_prefixes]]
        prefix = "**Heart**"
        locator = "open/heart"

        [[first.constants]]
        name = "κ"
        locator = "constant/kappa"

        [[second.genres]]
        token = "定理"
        kind = "theorem"

        [[second.markers]]
        role = "trace-note"
        text = "追注"

        [[second.heading_prefixes]]
        prefix = "Supplement "
        locator = "metadata/supplement"

        [[second.heading_prefixes]]
        prefix = "判负册"
        locator = "negative-register/batch"

        [[wm.headings]]
        role = "title"
        text = "Synthetic WM"

        [[wm.headings]]
        role = "appendix"
        text = "Synthetic appendix"

        [[wm.headings]]
        role = "audit"
        text = "Synthetic audit"
        """
        .Replace("[[first.", "[[" + FirstScheme + ".", StringComparison.Ordinal)
        .Replace("[[second.", "[[" + SecondScheme + ".", StringComparison.Ordinal);
}
