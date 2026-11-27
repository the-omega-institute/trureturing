using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.ErdosNicolas;

internal sealed class ErdosNicolasMainDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/erdosnicolas1989functions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Erdős–Nicolas divisor difference conjecture", H("The Erdős–Nicolas conjecture"),
        Blocks(Describe.Lean(
            DescribeId.Create("erdosnicolas-result"),
            DeclarationHandle.Create("D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas"),
            H("Every integer above 5040 satisfies the strict inequality"),
            StatementSource.FromAuthor(Disp(All("n", Nat(),
                Imp(Lt(D(5,0,4,0), V("n")),
                    Lt(Call("Hhat", V("n")), Call("card", Call("divisors", V("n")))))))),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(
                "Page 390 of the cited source: “We conjecture that for n > 5040, we have Ĥ(n) < τ(n).” "
                + "Here Ĥ(n) is the unordered reciprocal gap sum over all positive divisors and τ(n) "
                + "is their number. A rational positive semidefinite kernel controls cross-block "
                + "interactions. Strong induction and exact finite certificates discharge every "
                + "branch without an extra analytic or numerical hypothesis. The proof handles "
                + "arbitrary prime exponent order, including noncanonical integers. The six "
                + "certificate propositions are proved by the imported data modules and supplied "
                + "to good_of_finite_certificates; none remain as assumptions of this theorem. "
                + "The conditional classification also identifies the exact fourteen positive "
                + "exceptions. Numerical observations, literature priority, and further extensions "
                + "are distinguished in the problem dossier."))),
            DescribeRole.Theorem,
            openProblemResolutionClaim: new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("erdos-nicolas-1989-divisor-difference-sum"),
                ResolutionKind.Proved)))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
