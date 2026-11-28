using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hypergraphs;

internal sealed class BoseTriplingBurningRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hypergraphs/BoseTriplingBurningRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/burgess2026burningsteiner");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cyclic Steiner triple system of order 13 has ordinary burning number 5. Its Bose tripling has burning number 6.",
        H("Ordinary burning under Bose tripling"),
        Blocks(
            Describe.Lean(DescribeId.Create("bose-tripling-burning-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("Bose tripling implication"),
                StatementSource.FromAuthor(Disp(new Formula.Logic(
                    Named("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Section 5 asks whether only the stated geometric families can have increased ordinary burning number under doubling or tripling. "
                    + "This implication takes the tripling part with the cited Bose operation. Its blocks on pairs (x,i) are the vertical triples "
                    + "and the triples formed by (x,i), (y,i), and (complete(x,y),i+1) for distinct x and y, with layers modulo 3. "
                    + "In each ordinary round the source is absent from the preceding burned set, and propagation completes pairs from that set. "
                    + "Non-degeneracy quantifies over every inclusion-maximal nonempty proper subsystem."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bose-tripling-burning-refutation"),
                DeclarationHandle.Create(Prefix + "result"), H("An order-13 counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Named("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Use the translates modulo 13 of the triples {0,1,4} and {0,2,7}. Every nonblock triple generates the base system, "
                    + "so each maximal proper subsystem is a block. The base has lazy burning number 3 and every block has lazy burning number 2. "
                    + "The certified ordinary schedules have lengths 5 and 6. At most 8 points burn in four rounds, and counting pairs in the "
                    + "preceding burned set gives at most 37 in five rounds. Order 13 lies strictly between consecutive admissible orders "
                    + "in each geometric family, namely 7 and 15 for projective systems and 9 and 27 for affine systems."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("burgess-et-al-2026-bose-tripling-burning"),
                    ResolutionKind.Refuted)))));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula term) => Seq(Open, term, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), h = F.Id("H");
        Formula families = new Formula.Logic(Call("Projective", h), FormulaLogicOperator.Or, Call("Affine", h));
        return All("n", Named("Nat"), All("H", Call("Steiner", Call("Fin", n)),
            Implies(Less(D(0), n), Implies(Call("Nondegenerate", h),
                Implies(Less(Call("burning", h), Call("burning", Call("bose", h))), Parenthesized(families))))));
    }
}
