using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class QuarticEGFFixedPointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "OEIS A396804 has a unique zero-constant rational formal solution with natural EGF coefficients.",
        H("The Quartic EGF Fixed Point"),
        Blocks(
            Paragraph(Text("The superscript four in the source denotes four compositional "
                + "iterations. The zeroth iterate is the identity series X. The sequence a "
                + "is constructed in Nat first; no integrality premise is assumed.")),
            Note("encode", "Encoding EGF coefficients",
                "Encoding a rational sequence s means taking ordinary coefficient s(n)/n!. "
                + "Factorial normalization recovers s(n) exactly, including n=0."),
            Note("iterateComp", "Formal compositional iteration",
                "The zeroth iterate is X; each successor is f composed with the previous "
                + "iterate. When f has constant coefficient zero, every iterate does too."),
            Note("step_contract", "Contraction by one degree",
                "If two coefficient sequences agree below d, applying the coefficient "
                + "transformation for X exp(A fourth) gives agreement below d+1. "
                + "This follows from the prefix locality of integral composition."),
            Note("approximation", "Natural approximations",
                "Start with the natural sequence n, the EGF coefficients of X exp(X), "
                + "and repeatedly apply step. The use of Nat gives a separate integrality proof."),
            Note("a", "The stabilized sequence",
                "a(n) is coefficient n of approximation n+1. Prefix stability shows that "
                + "all later approximations have the same value."),
            Note("A", "The rational formal series",
                "A encodes the natural sequence a as sum a(n) X^n/n!. Its constant term is zero."),
            Note("integral_coefficients", "Independent natural integrality",
                "For every natural n, (a(n):Rat)=n! [X^n]A. This statement connects "
                + "the natural construction with ordinary rational coefficients."),
            Note("A_equation", "The exact source equation",
                "The constructed A has constant coefficient zero and satisfies "
                + "A=X*(exp Rat).subst(iterateComp A 4). Every substitution is justified."),
            Note("fixed_unique", "Uniqueness among rational series",
                "Any two zero-constant rational solutions agree through every finite degree "
                + "by contraction, and hence are equal. No coefficient integrality premise "
                + "is imposed on these competing solutions."),
            Note("unique_solution", "Existence and uniqueness",
                "The constructed A supplies existence; fixed_unique gives uniqueness. "
                + "Together these identify the formal series used in the final congruence."))));

    private static DocumentBlock Note(string name, string title, string prose) =>
        Describe.Remark(DescribeId.Create("quartic-egf-"
                + (name == "A" ? "series-a" : name.Replace('_', '-').ToLowerInvariant())),
            DeclarationHandle.Create(Prefix + name), H(title), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))));
}
