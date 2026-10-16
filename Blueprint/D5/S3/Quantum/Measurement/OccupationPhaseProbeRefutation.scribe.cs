using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class OccupationPhaseProbeRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/OccupationPhaseProbeRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A bound on all linear occupation phases need not bound every phase of a constrained activity law.",
        H("Joint occupation defeats linear phase probes"),
        Blocks(
            Describe.Lean(DescribeId.Create("occupation-phase-probe-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The probe sufficiency assertion"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The carrier contains all five-site binary words without adjacent occupied sites. "
                        + "Site one is the least significant bit. The activities are (100,1,100,1,100), "
                        + "the partition function is 1030504, and p(s) is the product of the occupied-site "
                        + "activities divided by this partition function.")),
                    Paragraph(Text("The normalized site weights are (368/2565,5101/17955,289/1995,5101/17955,368/2565). "
                        + "V(f) is sum_s p(s) f(s)^2 minus (sum_s p(s) f(s))^2. "
                        + "For zero-based bit positions i=0,...,4, E(f) sums p(s) w_i lambda_i/(1+lambda_i) times (f(s)-f(s+2^i))^2 over "
                        + "empty sites whose insertion stays in the same carrier. Every undirected "
                        + "edge is counted once from its empty endpoint.")),
                    Paragraph(Text("L(c)(s) is the sum of c_i s_i. All coefficients are real. "
                        + "The assertion extends a lower bound valid on every linear occupation function "
                        + "to every real phase function. Functions are defined on natural words, "
                        + "but their values outside the carrier do not enter either form."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("occupation-phase-probe-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The lower bound does not extend"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every linear occupation function, E(L(c))-V(L(c))/10 is a "
                        + "sum of fifteen squares with positive coefficients, divided by 962888835832892640. "
                        + "The five single-variable coefficients are 296233677576200,201992930717100,"
                        + "197414496485100,201992930717100,296233677576200, with the second and fourth "
                        + "variables scaled by 1/10. The remaining ten squares correspond to pairs "
                        + "of distinct occupation coefficients.")),
                    Paragraph(Text("The nonlinear function f(s)=(1-s_1)(1-s_3)+s_2 includes the joint "
                        + "occupation s_1 s_3. It has E(f)=8757839/207641403480 and "
                        + "V(f)=131365851/265484623504. Its quotient is "
                        + "132720413542/1557033067485, strictly below 1/10, so it contradicts "
                        + "the asserted extension.")),
                    Paragraph(Text("The two forms use the same positive law and the same legal insertion edges. "
                        + "The conclusion concerns the sufficiency of linear occupation probes. "
                        + "It makes no claim about a physical energy, experimental implementation, "
                        + "or failure of the separate comparison between the two spectral edges."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, Formula argument) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, argument, Close);

    private static Formula Bound(Formula function) => new Formula.Relation(
        new Formula.Fraction(Call("V", function), D(1, 0)),
        FormulaRelationOperator.LessThanOrEqual, Call("E", function));

    private static Formula ClaimFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula c = F.Id("c"), f = F.Id("f");
        Formula linear = Seq(Forall, Sp, c, Colon, Sp,
            Seq(Operatorname, Grp(F.Id("Fin")), Open, D(5), Close),
            Sp, To, Sp, real, Comma, Sp, Bound(Call("L", c)));
        Formula all = Seq(Forall, Sp, f, Colon, Sp, nat, Sp, To, Sp, real,
            Comma, Sp, Bound(f));
        return Disp(Seq(F.Id("claim"), Sp, Iff, Sp,
            Seq(Open, new Formula.Logic(Seq(Open, linear, Close),
                FormulaLogicOperator.Implies, Seq(Open, all, Close)), Close)));
    }
}
