using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class EmpiricalIdentifiabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Protocol outcomes determine exactly which model properties descend uniquely.",
        H("Empirical Identifiability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("empirical-identifiability"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/EmpiricalIdentifiability.empirical_identifiability"),
                H("Empirical quotient descent and residual obstruction"),
                StatementSource.FromAuthor(Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The empirical setoid is constructed from equality of every allowed "
                            + "protocol outcome, and the quotient and class map are the canonical "
                            + "ones for that source relation.")),
                    Paragraph(Text(
                        "A property descends to exactly one quotient map precisely when it is "
                            + "constant on every empirical-equivalence fiber. An empirically "
                            + "equivalent pair with different property values rules out every "
                            + "possible quotient factor.")),
                    Paragraph(Text(
                        "Pinned quotient constructors were applied directly; no source object is "
                            + "defined as the target conclusion."))),
                DescribeRole.Theorem),
            new DocumentBlock.Section(H("Can three coupling readings identify a matching scale?"), Blocks(
                Paragraph(Text(
                    "Consider three inverse gauge couplings at a fixed reference scale in a "
                    + "one-loop matching model. Write E for the change in their three readings "
                    + "multiplied by 2 pi. Let a be 2 pi times the change of the inverse unified "
                    + "coupling, and t the change in the log matching scale. With matching scale mu "
                    + "and heavy masses M_D and M_C, let k and c be the changes in log(M_D^2/mu^2) "
                    + "and log(M_C^2/mu^2). Allow the two positive ratios to vary independently. "
                    + "In a fixed threshold regime, assume E = a(1,1,1) + t b - k D/2 - c C/2 "
                    + "with b = (41/10,-19/6,-7), D = (2/15,2/3,1/3) and C = (2/15,0,1/3).")),
                Paragraph(Text(
                    "Equality of all three readings means E = 0. Ten times the first component "
                    + "minus ten times the third gives 111t + k + c = 0. Six times the second "
                    + "minus six times the third gives 23t - k + c = 0. Adding these equations "
                    + "fixes t = -c/67. The second difference then fixes k = 44c/67, and setting "
                    + "the second reading to zero gives a = 23c/134. Substitution in all three "
                    + "components gives zero for every real c. Thus the entire fiber through a "
                    + "given parameter point is its translate by c(23/134,-1/67,44/67,1), "
                    + "intersected with the parameter domain.")),
                Paragraph(Text(
                    "Take the protocol outcome to be the triple of readings and the property "
                    + "to be the log matching scale. At an interior parameter point, a sufficiently "
                    + "small nonzero c preserves the threshold regime and moves the log scale. "
                    + "These two points have the same outcome and different property values, "
                    + "so the scale cannot descend to their empirical quotient. An independent "
                    + "determination of either mass coefficient which varies along this line "
                    + "fixes the position on the fiber. The charge vectors and the one-loop "
                    + "matching law are inputs to this calculation.")))))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Compose(Formula left, Formula right) =>
        Seq(left, Sp, Circ, Sp, right);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Formula()
    {
        Formula protocol = F.Id("P");
        Formula theory = F.Id("Theta");
        Formula target = F.Id("Y");
        Formula outcome = F.Id("Out");
        Formula property = F.Id("T");
        Formula descend = F.Id("d");
        Formula classMap = F.Id("class");
        Formula left = F.Id("theta");
        Formula right = F.Id("thetaPrime");
        Formula quotient = Subscript(F.Id("Theta"), F.Id("emp"));
        Formula sameOutcome =
            Seq(Open, Forall, Sp, protocol, Comma, Sp,
                Apply(Apply(outcome, protocol), left), Sp, Eq, Sp,
                Apply(Apply(outcome, protocol), right), Close);
        Formula fiberConstancy =
            Seq(Open, Forall, Sp, left, Comma, Sp, right, Comma, Esc,
                sameOutcome, Sp, Rightarrow, Sp,
                Apply(property, left), Sp, Eq, Sp, Apply(property, right), Close);
        Formula descent = Seq(Exists, Bang, Sp, descend, Colon, Sp,
            Arrow(quotient, target), Comma, Sp,
            Apply(property, left), Sp, Eq, Sp,
            Apply(descend, Apply(classMap, left)));
        Formula badPair = Seq(
            Open, Exists, Sp, left, Comma, Sp, right, Comma, Esc,
            sameOutcome, Sp, Land, Sp,
            Apply(property, left), Sp, Neq, Sp, Apply(property, right), Close);
        Formula noDescent = Seq(Neg, Exists, Sp, descend, Colon, Sp,
            Arrow(quotient, target), Comma, Sp,
            Apply(property, left), Sp, Eq, Sp,
            Compose(descend, classMap));

        return Disp(Seq(
            Forall, Sp, protocol, Comma, Sp, theory, Comma, Sp, target, Comma, Esc,
            outcome, Colon, Sp, protocol, Sp, To, Sp, theory, Sp, To, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            property, Colon, Sp, Arrow(theory, target), Comma, Esc,
            Open, Open, descent, Close, Sp, Iff, Sp, fiberConstancy, Close, Sp, Land, Sp,
            Open, badPair, Sp, Rightarrow, Sp, noDescent, Close, Dot));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
