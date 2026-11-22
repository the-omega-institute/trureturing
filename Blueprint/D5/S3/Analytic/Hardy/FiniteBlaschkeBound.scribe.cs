using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Hardy;

internal sealed class FiniteBlaschkeBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Blaschke bound in the open disk", H("Finite Blaschke bound in the open disk"),
        Blocks(
            Describe.Lean(DescribeId.Create("bounded-function-at-finitely-many-zeros"),
                DeclarationHandle.Create("D5/S3/Analytic/Hardy/FiniteBlaschkeBound.norm_le_mul_prod"),
                H("Bound by the product of pseudohyperbolic distances"), StatementSource.FromAuthor(Bound()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/AnalyticClosure/garnett2007boundedanalytic")),
                Blocks(
                    Paragraph(Text("Let s be a finite set of indices and a an injective complex-valued family. Let f be holomorphic and bounded in norm by M on the open unit disk. If aₖ is in the disk and f(aₖ)=0 for every k in s, the displayed estimate holds at each z in the disk. An empty product is one.")),
                    Paragraph(Text("On a smaller closed disk containing the point and all specified zeros, divide out one disk factor at a time. Divided differences remove the singularity at each zero. Mathlib's canonical disk factors have unit modulus on the boundary circle, so the maximum modulus principle preserves M after each division. Taking the radii up to one gives the bound with the unit-disk factors."))),
                DescribeRole.Theorem))));

    private static Formula Bound()
    {
        Formula z = F.Id("z"), k = F.Id("k"), a = Seq(F.Id("a"), Underscore, Grp(k));
        Formula factor = new Formula.Fraction(Seq(z, Minus, a),
            Seq(D(1), Minus, Overline, Grp(a), Sp, z));
        return Disp(Seq(new Formula.Norm(new Formula.Apply(F.Id("f"), [z])), Sp, Le, Sp,
            F.Id("M"), Sp, Prod, Underscore, Grp(k, InMacro, Sp, F.Id("s")), Sp,
            new Formula.Norm(factor)));
    }
}
