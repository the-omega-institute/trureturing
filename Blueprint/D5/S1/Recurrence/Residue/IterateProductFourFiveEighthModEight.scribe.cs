using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class IterateProductFourFiveEighthModEightDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2026a396798");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every coefficient above degree one in the eighth compositional iterate of A396798 is divisible by eight.",
        H("The Eighth Compositional Iterate Modulo Eight"),
        Blocks(
            Paragraph(Text("Write I0(F)=X and I(k+1)(F)=Ik(F) composed with F. "
                + "The source is an ordinary integer formal series satisfying "
                + "A=X+I4(A)*I5(A), with zero constant coefficient. The product "
                + "is ordinary series multiplication, and no factorial scaling "
                + "is used. Let H(F)=X+I4(F)*I5(F). In the definition below, "
                + "iterateFunction(H,k,0) means H applied k times to zero, "
                + "and mk assembles a series from its coefficient function.")),
            Describe.Lean(DescribeId.Create("a396798-generating-series"),
                DeclarationHandle.Create(Prefix + "generatingSeries"),
                H("The source series"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("A"), Eq, Call("mk", Seq(F.Id("n"), Mapsto,
                        Call("coeff", F.Id("n"), Call("iterateFunction", F.Id("H"),
                            Seq(F.Id("n"), Plus, D(1)), D(0)))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The n-th coefficient is taken from "
                    + "H iterated n+1 times at the zero series. The result's "
                    + "proof establishes coefficient stabilization, the source "
                    + "equation and uniqueness among zero-constant fixed points."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a396798-eighth-iterate-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Hanna's eighth conjecture"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Colon, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    D(1), Lt, F.Id("n"), Implies, Sp, D(8), Sp, Mid, Sp,
                    Call("coeff", F.Id("n"), Call("iterate", F.Id("A"), D(8)))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural index n>1, the "
                    + "coefficient of the eighth compositional iterate is "
                    + "divisible by eight. Source uniqueness identifies A "
                    + "modulo four with X/(1-X). An exact integer quotient "
                    + "and square-zero iteration then yield the eighth iterate "
                    + "equal to X modulo eight. This resolves only the eighth "
                    + "comment of OEIS revision 12; the other comments retain "
                    + "their separate scopes and evidence."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a396798-eighth-iterate-mod-eight"),
                    ResolutionKind.Proved)))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
}
