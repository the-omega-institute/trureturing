using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class BurnolRationalDepthBudgetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaBridge/BurnolRationalDepthBudget.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact integer depth selection and rational support budgets for the existing full multi-orbit Weil family.",
        H("Rational Burnol Depth Budget"),
        Blocks(
            Describe.Lean(DescribeId.Create("burnol-rational-rationalquarterdepth"),
                DeclarationHandle.Create(Prefix + "rationalQuarterDepth"),
                H("Exact integer depth"),
                StatementSource.FromAuthor(Disp(F.Id("N0 = Nat.log 4 ((c*q)/(d*p)), with natural division."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This total function uses only natural arithmetic. Soundness requires d,p,q>0; no claim is made for zero denominators."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("burnol-rational-rationalburnolradius"),
                DeclarationHandle.Create(Prefix + "rationalBurnolRadius"),
                H("Rational support ledger"),
                StatementSource.FromAuthor(Disp(F.Id("L_N = (N+1) B + K in the rational numbers."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This computes the existing additive convolution support budget without selecting a new radius by compactness."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("burnol-rational-rationalquarterdepth-integer-sound"),
                DeclarationHandle.Create(Prefix + "rationalQuarterDepth_integer_sound"),
                H("Strict integer certificate"),
                StatementSource.FromAuthor(Disp(F.Id("d>0, p>0 and N0<=N imply c*q < d*p*4^(N+1)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the strict next-power bound for the floor logarithm, and natural division with remainder. The strict inequality handles exact powers of four correctly."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("burnol-rational-rationalquarterdepth-real-sound"),
                DeclarationHandle.Create(Prefix + "rationalQuarterDepth_real_sound"),
                H("Certified geometric decay"),
                StatementSource.FromAuthor(Disp(F.Id("For d,p,q>0 and C<=c/d, every N>=N0 satisfies 4^(-(N+1))*C < p/q."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Cross multiplication is performed only after denominator positivity. This replaces a classical eventual-smallness threshold with an executable integer formula."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("burnol-rational-rationalquarterdepth-full-gram-margin"),
                DeclarationHandle.Create(Prefix + "rationalQuarterDepth_full_gram_margin"),
                H("The actual full Gram at the computed depth"),
                StatementSource.FromAuthor(Disp(F.Id("For a valid frame, an actual Burnol packet and C_packet<=c/d, all N>=N0 and all a satisfy Re(a*G_N a)<=-(4-p/q) E(a)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply the existing coefficient-uniform remainder, retaining all cross terms, and the analytic multiplicity floor one. A strictly negative conclusion additionally needs p/q<4 and a nonzero coefficient vector."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("burnol-rational-rationalburnol-support-and-margin"),
                DeclarationHandle.Create(Prefix + "rationalBurnol_support_and_margin"),
                H("One computable support and error budget"),
                StatementSource.FromAuthor(Disp(F.Id("Certified rational support radii B,K and the majorant c/d imply support in [-L_N,L_N] together with the full Gram margin, for every a and N>=N0."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The support certificates refer to the actual peak and killer functions. The analytic majorant upper bound remains explicit here and must be derived by the analytic budget owner; it is never replaced by an unverified numerical estimate."))), DescribeRole.Theorem)), []));
}
