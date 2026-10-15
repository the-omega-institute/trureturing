using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.ProjectionRange;

internal sealed class LocalGramCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/ProjectionRange/LocalGramCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local Gram coordinates for a continuous constant-rank matrix field",
        H("Local Gram coordinates for a continuous constant-rank matrix field"),
        Blocks(
            Paragraph(Text("In the formula, LocalGramData consists of all E, its topology, finite decidable n, Q:E to Matrix n n C, s subset E, x0 in s, positive semidefiniteness of Q on s, ContinuousWithinAt Q s x0, and eventual equality of the rank of Q(y) to that of Q(x0) in nhdsWithin s x0. Injection(q) is the type of injections from Fin k into n, where k is the rank of Q(x0). OpenNeighborhood(q) consists of open U with x0 in U intersect s. LocalDomain(q,U) is U intersect s. Selected(q,J,y) is the n by k matrix with entry Q(y)(i,J(j)); Gram is its conjugate transpose times itself. Positive(q,y) means Q(y).PosSemidef. UnitGram means IsUnit of this Gram matrix, including the empty matrix. SameSpan means that the complex span of the selected columns equals the complex span of all columns of Q(y). These definitions bind every symbol in the formula and retain the relative-neighborhood hypothesis.")),
            Paragraph(Text("Let E be any topological space, n any finite decidable index type, s a subset of E, and x0 a point of s. Let Q:E -> Matrix n n C be positive semidefinite on s, continuous within s at x0, with rank eventually equal to its rank k at x0 in the relative neighborhood filter.")),
            Paragraph(Text("There exist an injection J:Fin k -> n and an open set U containing x0 such that for every y in U intersect s the selected-column matrix C(y) has invertible Gram matrix C(y)* C(y), and its columns span exactly the columns of Q(y). The conclusion also preserves positive semidefiniteness of Q(y). All quantifiers of the Lean theorem are preserved in this authored presentation; n and k may be empty or zero.")),
            Paragraph(Text("The selection is fixed throughout this neighborhood, not chosen separately at every nearby point. Invertibility persists because the Gram determinant is continuous and nonzero at x0. Equality of spans follows from inclusion and equal finite dimension. The projection-range constructor consumes this theorem with s equal to the whole base and derives positivity from Hermitian idempotence.")),
            Describe.Lean(
                DescribeId.Create("exact-original-local-gram-certificate"),
                DeclarationHandle.Create(Prefix + "exact_original_local_gram_certificate"),
                H("exact_original_local_gram_certificate"),
                StatementSource.FromAuthor(GramFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Select a maximal independent subfamily of columns; index it by Fin rank. Its Gram determinant is nonzero at x0 and remains nonzero on a relative neighborhood. Gram invertibility makes selected columns independent at nearby points. Their span is contained in the full column span and has the same constant finite rank, hence the spans agree. Extract an open neighborhood from nhdsWithin."))),
                DescribeRole.Theorem)),
        []));

    private static Formula GramFormula()
    {
        Formula q = F.Id("q"), j = F.Id("J"), u = F.Id("U"), y = F.Id("y");
        return F.Disp(F.Seq(
            F.Forall, F.Sp, q, F.InMacro, F.Sp, F.Id("LocalGramData"), F.Comma, F.Sp,
            F.Exists, F.Sp, j, F.InMacro, F.Sp, Call("Injection", q), F.Comma, F.Sp,
            F.Exists, F.Sp, u, F.InMacro, F.Sp, Call("OpenNeighborhood", q), F.Comma, F.Sp,
            F.Forall, F.Sp, y, F.InMacro, F.Sp, Call("LocalDomain", q, u), F.Comma, F.Sp,
            F.Grp(Call("Positive", q, y), F.Sp, F.Land, F.Sp,
                Call("UnitGram", q, j, y), F.Sp, F.Land, F.Sp,
                Call("SameSpan", q, j, y)), F.Dot));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
