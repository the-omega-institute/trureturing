using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class RationalFarkasDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S0/Certificates/RationalFarkas.infeasible_of_certificate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact nonnegative rational dual weights certify infeasibility of finite "
            + "linear inequality systems.",
        H("Exact Rational Farkas Certificates"),
        Blocks(Describe.Lean(
            DescribeId.Create("rational-farkas-certificate"),
            DeclarationHandle.Create(Declaration),
            H("A negative rational dual combination excludes every primal solution"),
            StatementSource.FromAuthor(InfeasibilityFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The primal system consists of finitely many exact rational inequalities A x less than or equal to b.")),
                Paragraph(Text(
                    "A certificate assigns a nonnegative rational weight to every row, annihilates every variable coefficient after weighted summation, and makes the weighted right-hand side strictly negative.")),
                Paragraph(Text(
                    "Any feasible point would make the same weighted right-hand side nonnegative. Lean checks the finite sum rearrangement and contradiction using exact ordered-field arithmetic."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula InfeasibilityFormula() => Disp(Seq(
        Forall, Sp, F.Id("A"), Comma, Sp, F.Id("b"), Comma, Sp,
        Call("Certificate", F.Id("A"), F.Id("b")), Sp, Rightarrow, Sp,
        Neg, Sp, Exists, Sp, F.Id("x"), Comma, Sp,
        Call("LinearFeasible", F.Id("A"), F.Id("b"), F.Id("x")), Dot));

}
