using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class EtaCuspMultiplierDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/mathlib2026etacusps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constant cusp multipliers with exact eta and reciprocal Euler normalization.",
        H("EtaCuspMultiplier"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eta-unit-multiplier"),
                DeclarationHandle.Create("D5/S3/Arith/ModularForms/EtaCuspMultiplier.eta_unit_multiplier"),
                H("One constant on the full upper half-plane"),
                StatementSource.FromAuthor(Disp(Seq(Call("eta", Call("act", Gamma, Tau)), Sp, Eq, Sp, Xi, Sp, Cdot, Sp, Call("sqrt", Call("denom", Gamma, Tau)), Sp, Cdot, Sp, Call("eta", Tau)))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every gamma in SL(2,Z) with c=gamma(1,0)>0, there exists a complex xi with xi^24=1 and norm(xi)=1 such that eta(gamma tau)=xi sqrt(c tau+d) eta(tau) for every tau in the upper half-plane. The root is principal.")),
                    Paragraph(Text("The existing level-one discriminant supplies eta(gamma tau)^24=(c tau+d)^12 eta(tau)^24. The eta quotient is continuous and nonzero; its image is contained in the finite discrete set of twenty-fourth roots of unity. Connectedness forces a single value on the entire upper half-plane. This is the missing constancy inference, rather than an assumed transformation law. The proof does not infer a general Dedekind-sum formula."))),
                DescribeRole.Theorem))));

    private static Formula Div(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
