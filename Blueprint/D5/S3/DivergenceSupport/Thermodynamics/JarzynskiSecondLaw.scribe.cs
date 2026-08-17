using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.DivergenceSupport.Thermodynamics;

internal sealed class JarzynskiSecondLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a finite probability law, the Jarzynski equality implies the mean-work lower bound by convexity of the exponential.",
        H("Jarzynski Equality Implies the Mean-Work Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("jarzynski-equality-implies-the-mean-work-lower-bound"),
                DeclarationHandle.Create(
                    "D5/S3/DivergenceSupport/Thermodynamics/JarzynskiSecondLaw."
                        + "jarzynski_implies_mean_work_lower_bound"),
                H("The exponential equality casts the second-law inequality"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Comma, Sp,
                    F.Id("s"), InMacro, Sp,
                    Operatorname, Grp(F.Id("Finset")), Open, Iota, Close, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("W"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Beta, Comma, Sp, Delta, Sp, F.Id("F"), InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open, Forall, Sp, F.Id("i"), InMacro, Sp, F.Id("s"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("i"), InMacro, Sp, F.Id("s")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Sp, Eq, Sp, D(1),
                    Sp, Land, Sp, D(0), Lt, Sp, Beta, Sp, Land, RowBreak,
                    Sum, Underscore, Grp(F.Id("i"), InMacro, Sp, F.Id("s")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Sp,
                    Exp, Sp, Open, Minus, Beta, Sp,
                    F.Id("W"), Open, F.Id("i"), Close, Close,
                    Sp, Eq, Sp, Exp, Sp, Open, Minus, Beta, Sp, Delta, Sp, F.Id("F"), Close,
                    Sp, Rightarrow, RowBreak,
                    Delta, Sp, F.Id("F"), Sp, Le, Sp,
                    Sum, Underscore, Grp(F.Id("i"), InMacro, Sp, F.Id("s")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Sp,
                    F.Id("W"), Open, F.Id("i"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p be nonnegative and normalized on the finite set s, let beta be "
                            + "positive, and suppose the weighted exponential work average is "
                            + "exactly exp(-beta times the free-energy difference). Convexity of "
                            + "the exponential puts exp(-beta times mean work) below that average. "
                            + "Strict monotonicity of exp and positivity of beta then give the "
                            + "displayed mean-work lower bound.")),
                    Paragraph(Text(
                        "The Lean proof applies Mathlib's finite weighted Jensen theorem "
                            + "ConvexOn.map_sum_le to convexOn_exp. It formalizes only the "
                            + "Jarzynski-to-mean-work implication; no Crooks relation, fluctuation "
                            + "model, or open-system monotonicity claim is included."))),
                DescribeRole.Theorem
            )),
        []));
}
