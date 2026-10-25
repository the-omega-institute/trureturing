using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class SharedEnergyGapBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Labelled indecomposable zero-weight exponents have degree at most twice m minus one.",
        H("Shared Energy Indecomposable Bound"), Blocks(
            Describe.Lean(DescribeId.Create("indecomposable-degree-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/SharedEnergyGapBound.indecomposable_degree_bound"),
                H("The bound includes zero units and repeated numerical gaps"),
                StatementSource.FromAuthor(Bound()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The domain consists of actual labelled natural exponents on all nine ordered matrix coordinates "
                    + "for the fixed energy basis with energies zero, one and m. A nonzero zero-weight exponent is indecomposable "
                    + "when every zero-weight subexponent is zero or the whole exponent. If a diagonal coordinate occurs, its unit "
                    + "already forces degree one. If both directions of a coordinate occur, their pair forces degree two. "
                    + "Otherwise transpose if necessary to remove the positive m coordinate. The remaining sign patterns admit "
                    + "explicit zero-weight subexponents with degree at most twice m minus one. Minimality forces equality with "
                    + "one of those subexponents. Every step retains coordinate identity, so the coincident numerical gaps at m equal "
                    + "to two remain included. The degree bound combines with shared-moment extraction and support-wise phase reconstruction to give the all-state compact-orbit bound."))),
                DescribeRole.Theorem))));
    private static Formula C(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Bound()
    {
        var m = F.Id("m"); var a = F.Id("a");
        return Disp(Seq(Forall, Sp, m, InMacro, C("Nat"), Comma,
            D(2), Leq, Sp, m, Sp, Implies, Sp, Forall, Sp, a, InMacro, C("Exponent"), Comma,
            C("Indecomposable", m, a), Sp, Implies, Sp,
            C("degree", a), Leq, Sp, D(2), Cdot, Sp, m, Minus, D(1)));
    }
}
