using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class AraujoBrauerCompleteMappingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerCompleteMapping.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/araujo2026brauerexistence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Brauer and partial Brauer monoids admit complete mappings exactly in degree one and degrees at least four.",
        H("Complete mappings of Brauer and partial Brauer monoids"),
        Blocks(
            Describe.Lean(DescribeId.Create("araujo-brauer-existence-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The whole-monoid existence question"),
                StatementSource.FromAuthor(Disp(Equal(Named("claim"), Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Problem 15.11, printed page 61: \"Classify complete mappings for "),
                    Math(Seq(Mathcal, Grp(F.Id("B")), Underscore, Grp(F.Id("n")))), Text(" and "),
                    Math(Seq(Mathcal, Grp(F.Id("PB")), Underscore, Grp(F.Id("n")))),
                    Text(". In view of the Hall--Paige theorem, the unresolved proper factors are those of ranks "),
                    Math(D(2)), Text(" and "), Math(D(3)),
                    Text(" which occur in the corresponding monoid. Determine also for which values of "),
                    Math(F.Id("n")), Text(" the whole monoid has a complete mapping.\" The question asks for the degrees; the numerical classification is the answer proved below. The two existence clauses construct monoid structures with the exterior-connectivity product. The remaining clauses quantify over every such structure. Labels in Fin n represent the paper's labels shifted by one; false and true identify its unprimed and primed rows. CompleteMapping is applied with its carrier and semigroup structure displayed explicitly."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("araujo-brauer-existence-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The existence classification"),
                StatementSource.FromAuthor(Disp(ClaimBody())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Rank fibres are assembled from transversals. The exceptional rank-two and rank-three Brauer factors use supported cycles with one triangle of negative transport sign. Partial Brauer factors in these ranks have even index. Unit groups exclude degrees two and three, and identity maps supply degree one."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("araujo-brauer-complete-mapping"), ResolutionKind.Proved)))));

    private static Formula ClaimBody() => All("n", Seq(Mathbb, Grp(F.Id("N"))),
        Imp(Seq(D(1), Sp, Leq, Sp, F.Id("n")),
            And(ExistsStructure("BrauerSourceMonoid"),
                And(ExistsStructure("PartialBrauerSourceMonoid"),
                    And(Classification("B", "BrauerSourceMonoid", "Brauer"),
                        Classification("PB", "PartialBrauerSourceMonoid", "PartialBrauer"))))));

    private static Formula ExistsStructure(string name) => Seq(Exists, Sp,
        Parenthesized(Seq(Colon, Sp, Call(name, F.Id("n")))), Comma, Sp, Named("True"));

    private static Formula Classification(string variable, string structure, string carrier) =>
        All(variable, Call(structure, F.Id("n")),
            new Formula.Logic(Parenthesized(Seq(Exists, Sp, Alpha, Sp, Colon, Sp,
                Parenthesized(Seq(Call(carrier, F.Id("n")), Sp, To, Sp, Call(carrier, F.Id("n")))),
                Comma, Sp, Call("CompleteMapping", Call(carrier, F.Id("n")),
                    Seq(F.Id(variable), Dot, Named("algebra"), Dot, Named("toSemigroup")), Alpha))),
                FormulaLogicOperator.Iff,
                Parenthesized(new Formula.Logic(Equal(F.Id("n"), Num(1)), FormulaLogicOperator.Or,
                    Seq(D(4), Sp, Leq, Sp, F.Id("n"))))));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(variable), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
}
