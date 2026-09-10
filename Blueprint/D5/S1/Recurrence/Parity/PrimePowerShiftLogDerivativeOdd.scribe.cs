using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class PrimePowerShiftLogDerivativeOddDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivativeOdd.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2026a393867");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every coefficient of the logarithmic derivative defining OEIS A393867 is odd.",
        H("All Terms of OEIS A393867 Are Odd"),
        Blocks(
            Paragraph(Text("Let F be the integer series generatingSeries from "
                + "PrimePowerShiftLogDerivative. Its constant coefficient is one, and "
                + "coeff(n,F^prime(n)) = prime(n) coeff(n-1,F^prime(n)) for n >= 1. "
                + "The nth term a393867(n) is coeff(n-1,F'/F). The cast in the first "
                + "formula is reduction of an integer to ZMod 2; Odd in the second "
                + "formula is integer oddness. The results use this original series "
                + "and its one-based sequence indexing.")),
            Describe.Lean(DescribeId.Create("a393867-generating-coeff-pair"),
                DeclarationHandle.Create(Prefix + "generating_coeff_pair"),
                H("Paired Coefficients Modulo Two"), StatementSource.FromAuthor(PairFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Over ZMod 2 put D(B)=(1+X)B'-B. For an odd "
                    + "prime p, the power rule gives D(F^p)=D(F)F^(p-1). Every odd "
                    + "coefficient of D(B) vanishes identically. At even degree k>0, "
                    + "the source equation at n=k+1 gives coeff(k,D(F^p))=0. "
                    + "Strong induction removes the lower coefficients of D(F); "
                    + "the constant coefficient of F^(p-1) is one, so the kth "
                    + "coefficient of D(F) also vanishes. At k=0 the integral equation "
                    + "with p=2 first gives F_1=1. Extracting each even coefficient "
                    + "of D(F)=0 proves the displayed pair equality.")))),
            Describe.Lean(DescribeId.Create("a393867-all-terms-odd"),
                DeclarationHandle.Create(Prefix + "a393867_odd"),
                H("The Oddness Conjecture"), StatementSource.FromAuthor(OddFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The paired coefficients give (1+X)F'=F "
                    + "after reduction modulo two. Multiplying by the mapped unit "
                    + "inverse of F gives (1+X)L=1, where L is the reduction of "
                    + "the original integer logarithmic derivative. Its constant "
                    + "coefficient is one, and consecutive coefficients are equal, "
                    + "so every coefficient is one in ZMod 2. The integer terms "
                    + "are therefore odd. This proves exactly the second A393867 "
                    + "comment, 'Conjecture: all terms are odd.'"))),
                DescribeRole.Theorem, new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a393867-all-terms-odd"), ResolutionKind.Proved)))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Bound(string n) => Seq(Forall, Sp, F.Id(n), Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp);
    private static Formula ReducedCoeff(Formula k) => Call("cast", Call("coeff", k, F.Id("F")));
    private static Formula PairFormula() => Disp(Seq(Bound("m"),
        ReducedCoeff(Mul(D(2), F.Id("m"))), Sp, Eq, Sp,
        ReducedCoeff(Add(Mul(D(2), F.Id("m")), D(1)))));
    private static Formula OddFormula() => Disp(Seq(Bound("n"), D(1), Sp, Le, Sp, F.Id("n"),
        Sp, Implies, Sp, Call("Odd", Call("a393867", F.Id("n")))));
}
