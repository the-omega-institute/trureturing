using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;
internal sealed class SolidResolvingTournamentDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ConceptDynamics/hakanenpavan2026solid");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SolidResolvingTournament", H("SolidResolvingTournament"), Blocks(
            Describe.Lean(DescribeId.Create("claim"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournament.claim"), H("claim"),
                StatementSource.FromAuthor(Disp(EqF(X("claim"), ClaimBody()))), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("We have βₛ(K⃗₆) ≥ 4, βₛ(K⃗₇) ≥ 5,  βₛ(K⃗₈) ≥ 5, βₛ(K⃗₉) ≥ 5, βₛ(K⃗₁₀) ≥ 5 and βₛ(K⃗₁₁) ≥ 6. (Conjecture 3.4, page 8.) Each R ranges over all relations on Fin n; IsTournament requires no loops and exactly one arc between distinct vertices. The six orders are 6, 7, 8, 9, 10 and 11."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournament.result"), H("result"),
                StatementSource.FromAuthor(Disp(ClaimBody())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The six lower bounds hold for every tournament at the indicated orders. A solid set with three, four or five landmarks forces total order at most four, six or ten. Outside vertices give mutually incomparable distance profiles. Chain covers of the profiles for each induced landmark tournament bound their number; terminal components also cover infinite distances."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("solid-resolving-tournament"), ResolutionKind.Proved)))));
    private static Formula X(string n) => F.Id(n);

    private static Formula N(int n) => new Formula.Number(n);

    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);

    private static Formula Call(string f, params Formula[] xs) => xs.Length == 0 ? Seq(Operatorname, Grp(X(f))) : App(Seq(Operatorname, Grp(X(f))), xs);

    private static Formula P(Formula p) => Parenthesized(p);

    private static Formula Parenthesized(Formula p) => Seq(Left, Open, p, Right, Close);

    private static Formula All(string n, Formula t, Formula p) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, p);

    private static Formula A(Formula p, Formula q) => new Formula.Logic(p, FormulaLogicOperator.And, q);

    private static Formula Imp(Formula p, Formula q) => new Formula.Logic(p, FormulaLogicOperator.Implies, q);

    private static Formula EqF(Formula p, Formula q) => new Formula.Relation(p, FormulaRelationOperator.Equal, q);

    private static Formula LeF(Formula p, Formula q) => new Formula.Relation(p, FormulaRelationOperator.LessThanOrEqual, q);

    private static Formula Arr(Formula a, Formula b) => Seq(P(a), Sp, To, Sp, P(b));

    private static Formula FinT(Formula k) => Call("Fin", k);

    private static Formula ClaimBody()
    {
        int[] ns = [6, 7, 8, 9, 10, 11], bs = [4, 5, 5, 5, 5, 6];
        Formula Clause(int i) => All("R", Arr(FinT(N(ns[i])), Arr(FinT(N(ns[i])), X("Prop"))), Imp(Call("IsTournament", X("R")), LeF(N(bs[i]), Call("solidMetricDimension", X("R")))));
        Formula result = Clause(5);
        for (int i = 4; i >= 0; i--) result = A(Clause(i), result);
        return result;
    }


}
