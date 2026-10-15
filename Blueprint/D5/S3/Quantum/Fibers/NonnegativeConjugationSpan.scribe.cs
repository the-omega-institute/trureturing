using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class NonnegativeConjugationSpanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Commutator jets lie in the span of actual nonnegative-time matrix conjugations.",
        H("Nonnegative Waits and Commutator Jets"),
        Blocks(Describe.Lean(
            DescribeId.Create("nonnegative-conjugation-span"),
            DeclarationHandle.Create("D5/S3/Quantum/Fibers/NonnegativeConjugationSpan.commutator_jets_in_nonnegative_span"),
            H("Every commutator jet belongs to the observation span"),
            StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Colon, F.Id("Type"), Comma,
                    OpenBracket, C("Fintype", F.Id("n")), CloseBracket,
                    OpenBracket, C("DecidableEq", F.Id("n")), CloseBracket, Comma,
                    Forall, Sp, F.Id("A"), Comma, F.Id("X"), Colon, C("RealMatrix", F.Id("n")), Comma,
                    Forall, Sp, F.Id("k"),
                    InMacro, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, F.Id("t"), InMacro, Sp,
                    Seq(Mathbb, Grp(F.Id("R"))), Comma, D(0), Leq, Sp, F.Id("t"), Rightarrow, Sp,
                    C("conjugate", F.Id("A"), C("iterate", C("commutator", F.Id("A")),
                        F.Id("k"), F.Id("X")), F.Id("t")), InMacro, Sp,
                    C("observationSpan", F.Id("A"), F.Id("X"))))), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For arbitrary finite real matrices A and X, conjugate X by the exponential of t A, with inverse exponential on the left. The observation span uses only nonnegative real times. Its finite dimension makes it closed.")),
                Paragraph(Text("The derivative is the same conjugation of the commutator X A minus A X. Difference quotients within the nonnegative half-line remain in the observation span. Closure puts their derivatives there, and induction gives every iterated commutator at every nonnegative time, including time zero.")),
                Paragraph(Text("This analytic implication allows exact algebraic spanning information about commutator jets to imply a statement about actual waiting effects. It does not add a derivative measurement to the menu, and it does not by itself certify the rank of a particular five-mode family."))),
            DescribeRole.Theorem))));

    private static Formula C(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
