using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class Erdos203ConditionalCapacityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every original 252-phase vector, the uncovered fraction on period M=17599117536000 is at least 41512904387/2792167686000. No single globally fixed phase vector covers all integer exponent points. These conclusions concern the specified 252 rows only.",
        H("A uniform positive hole bound for the original 252 rows"),
        Blocks([
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203conditionalcapacity-0"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203ConditionalCapacity.Holes"),
                H("Uncovered points at the original phases"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Holes c is the set of points in (ZMod M) squared missed by every one of the 252 original linear congruences at the unchanged phase vector c."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203conditionalcapacity-1"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203ConditionalCapacity.globalCover"),
                H("Existence of a globally fixed covering phase vector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The claim asks whether there exists one original phase vector c such that for every pair of integers x,y, some original row hits its assigned phase c i. The existential phase vector is chosen before both exponent coordinates. This is the construction possibility for the supplied rows, not a published conjecture or the whole Erdos 203 assertion."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203conditionalcapacity-3"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203ConditionalCapacity.uniform_hole_bound"),
                H("The exact uniform positive gap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every unchanged original phase vector c, 41512904387 times M squared is at most 2792167686000 times the cardinality of Holes c. Equivalently, every c has at least 4604933957031786373632000 holes. The canonical conditional union estimate uses all 96 certificates defined in this module; one common translation gives a bijection of hole sets and returns the bound to the original phases. The certificate equations and digit bounds give the required arithmetic inequalities. The bound does not assert simultaneous attainment of the separate histogram maxima or the minimum actual hole count."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203conditionalcapacity-2"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203ConditionalCapacity.result"),
                H("No global covering phase vector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The closed theorem has type Not globalCover. Given a proposed covering phase vector, it normalizes that vector, uses the certified canonical conditional union estimate to construct a missed torus point, lifts both coordinates to integers, and translates them back together. The original-row event equivalence contradicts coverage at that integer pair. The 285-row composition and the whole Erdos 203 problem remain outside the conclusion."))),
                DescribeRole.Theorem),
            .. Enumerable.Range(0, 96).Select(k => Describe.Lean(
                DescribeId.Create("erdos203-certificate-" + k.ToString(System.Globalization.CultureInfo.InvariantCulture)),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203ConditionalCapacity.certificate" + k.ToString(System.Globalization.CultureInfo.InvariantCulture)),
                H("Arithmetic certificate for class " + k.ToString(System.Globalization.CultureInfo.InvariantCulture)),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The record contains the 24 horizontal polynomials, 129 projected histograms, their upper bounds, and the missed six-row count for this canonical class. Its five proof fields establish the polynomial equations, projection equations, digit bounds, count equation and exact scaled capacity deficit."))),
                DescribeRole.Definition))]),
        []));
}
