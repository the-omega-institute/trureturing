using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.Diagonalization;

internal sealed class BooleanStreamDiagonalDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Lawvere =
        LibraryNoteRef.Create("D5/L/Diagonal/lawvere1969diagonal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Boolean diagonal negation exceeds every proposed enumeration of infinite streams.",
        H("Boolean Stream Diagonalization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("boolean-stream-diagonal-exceeds-every-history"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Diagonalization/BooleanStreamDiagonal.boolean_stream_diagonal_exceeds_every_history"),
                H("The diagonal stream exceeds every history layer"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("P"), Colon, Sp, Mathbb, Grp(F.Id("N")), To,
                    Sp, Mathbb, Grp(F.Id("N")), To, Sp,
                    Operatorname, Grp(F.Id("Bool")), Comma, Sp,
                    F.Text, Grp(F.Id("let"), Sp), Sp,
                    F.Id("D"), Open, F.Id("h"), Close, Sp, Colon, Eq, Sp,
                    Operatorname, Grp(F.Id("not")), Open,
                    F.Id("P"), Open, F.Id("h"), Comma, F.Id("h"), Close, Close, Semi, Sp,
                    Open, Forall, Sp, F.Id("h"), Comma, Sp, F.Id("D"), Sp, Neq, Sp,
                    F.Id("P"), Open, F.Id("h"), Close, Close, Sp, Land, Sp,
                    Neg, Operatorname, Grp(F.Id("Surjective")), Open, F.Id("P"), Close,
                    Sp, Land, Sp, Neg, Exists, Sp, F.Id("V"), Colon, Sp,
                    Mathbb, Grp(F.Id("N")), To, Sp, Mathbb, Grp(F.Id("N")), To, Sp,
                    Operatorname, Grp(F.Id("Bool")), Comma, Sp,
                    Operatorname, Grp(F.Id("Computable")), Underscore, Num(2),
                    Open, F.Id("V"), Close, Sp, Land, Sp,
                    Forall, Sp, F.Id("trajectory"), Colon, Sp,
                    Mathbb, Grp(F.Id("N")), To, Sp,
                    Operatorname, Grp(F.Id("Bool")), Comma, Sp,
                    Operatorname, Grp(F.Id("Computable")),
                    Open, F.Id("trajectory"), Close, Sp, Rightarrow, Sp,
                    Exists, Sp, F.Id("code"), Comma, Sp,
                    F.Id("V"), Open, F.Id("code"), Close, Sp, Eq, Sp,
                    F.Id("trajectory"), Dot))),
                AssessedProvenance.FromLiterature(Lawvere),
                Blocks(
                    Paragraph(Text(
                        "For an arbitrary history-indexed listing P of Boolean streams, define D at "
                        + "index h by negating P's h-th row at its h-th coordinate. Equality D = P(h) "
                        + "would force not(P(h,h)) = P(h,h), so D differs from every listed row. This "
                        + "is the source atom's explicit diagonal property.")),
                    Paragraph(Text(
                        "The missing diagonal row proves that the full stream space is not exhausted by "
                        + "the history listing. For the program-level clause, take any computable total "
                        + "evaluator V. Its negated diagonal is again a computable Boolean trajectory, so "
                        + "a claim that V outputs every computable trajectory supplies a code e for that "
                        + "diagonal and contradicts V(e,e). This is the source's self-diagonal index e.")),
                    Paragraph(Text(
                        "Pinned Mathlib and D5 were searched before proving. Mathlib's "
                        + "Function.exists_fixed_point_of_surjective is the exact abstract Lawvere engine "
                        + "used to refute both surjectivity claims. The neighboring D5 theorem "
                        + "SyntaxSemanticsBoundary.same_layer_predicates_not_enumerable treats predicates "
                        + "on an arbitrary code type; it does not expose this Boolean stream witness or "
                        + "the evaluator clause, so it is related but not a duplicate."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Computability/SyntaxSemanticsBoundary"))]));
}
