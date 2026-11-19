using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class MercaClassNumberCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithUnits/MercaClassNumberCriterion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/mazhang2026quartic");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Class Numbers and the Full Centered Criterion",
        H("Actual Class Numbers and the Full Centered Criterion"),
        Blocks(
            Node("delta", "The exact signed class-number difference", DescribeRole.Definition, "Delta is the integer half of the genuine imaginary quadratic ideal class number minus m. The upstream equality proves that the half is exact."),
            Node("delta_congruence", "The signed congruence", DescribeRole.Theorem, "The actual Delta is congruent to k+t modulo four. The literal imaginary quarter sum counts nonresidues modulo two, and the universal quarter identity supplies the required congruence."),
            Node("equality_criterion", "Equality before sign", DescribeRole.Theorem, "Equal coordinate magnitudes are equivalent to the genuine relative class number being exactly k squared. Merely being a square is insufficient."),
            Node("sign_criterion", "The two sign branches", DescribeRole.Theorem, "Under equal magnitudes, Delta is two modulo four exactly when k=t and zero modulo four exactly when k=-t. Oddness of k distinguishes both cases."),
            Node("centered_criterion", "The full class-number centered criterion", DescribeRole.Theorem, "For every distinct prime q, the literal centered sum on H is equivalent to chi(q)=1, or the actual quotient equals k squared with Delta two and chi(q)=-i, or the actual quotient equals k squared with Delta zero and chi(q)=i. Together with the existing CRT structure and generator theorem, this retains all admissible odd q including three, on either side of r."),
            Node("conjugate_invariants", "The actual fixed field survives conjugation", DescribeRole.Theorem, "Conjugation fixes K and its literal cyclotomic fixed field, hence the real subfield and genuine class numbers. The real coordinate is unchanged and the imaginary coordinate is negated, with the same actual norm identity."),
            Node("conjugate_centered_criterion", "The conjugate centered branches", DescribeRole.Theorem, "With chi-minus(2)=-i, the additional Delta-two centered branch uses chi-minus(q)=i and the Delta-zero branch uses -i. The same actual quotient, imaginary quadratic class number and Delta occur. The existing conjugate-coordinate theorem explicitly matches the ordered cosets K,2K,-K,-2K with values 1,-i,-1,i."),
            Node("generator_criterion", "The actual eligible source period", DescribeRole.Theorem, "For each admissible odd q, an actual generator of H exists, has the source coprimality property, and its powers through one full order enumerate H once. Its literal least-positive residue sum therefore has the full class-number centered criterion, including admissible q=3."),
            Paragraph(Text("Historical credit: Haobo Ma and Wenlin Zhang, CC BY 4.0; Joseph S. Farland criterion/sign attribution and OEIS terms; joint Ma-Merca-Zhang application; Louboutin, Hudson and classical class-number sources. Yao Xu/catalan-lean4 supplier notices remain intact. No novelty, priority, consent or publication claim is made.")),
            Paragraph(Text("The source-owner four-slot audits remain unfinished at https://github.com/the-omega-institute/trureturing/issues/27629. Kernel evidence and author exposition do not replace independent whole-result acceptance. Separate analytic density results of the MMZ preprint are outside this assignment.")))));
    private static DocumentBlock Node(string name, string title, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("merca-class-number-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), role);
}
