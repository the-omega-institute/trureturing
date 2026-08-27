using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Fibers;

internal sealed class CanonicalAdmissibleFiberDecompositionDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Fibers/CanonicalAdmissibleFiberDecomposition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A readout canonically decomposes all states and admissible states into dependent fibers.",
        H("Canonical Admissible Fiber Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("admissible-concept-fiber"),
                DeclarationHandle.Create(DeclarationPrefix + "AdmissibleConceptFiber"),
                H("Admissible concept fiber"),
                StatementSource.FromAuthor(AdmissibleFiberFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The admissible fiber over b contains a state x, evidence that x is "
                        + "admissible, and an equality q(x) = b."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("canonical-admissible-fiber-decomposition"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "canonical_admissible_fiber_decomposition"),
                H("Ordinary and admissible states decompose into canonical fibers"),
                StatementSource.FromAuthor(DecompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an arbitrary readout q and admissibility predicate Adm, the public "
                            + "statement exposes both dependent-sum equivalences and their forward "
                            + "and inverse computation rules.")),
                    Paragraph(Text(
                        "The ordinary equivalence is the frozen family source of truth. The second "
                            + "equivalence sends an admissible state to its readout, its state, its "
                            + "admissibility evidence, and the reflexive fiber witness.")),
                    Paragraph(Text(
                        "Each equivalence is unique among equivalences satisfying those computation "
                            + "rules. No surjectivity, section, quotient, or choice is assumed."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create(
                "D5/S3/ConceptDynamics/Fibers/CanonicalDependentFiberEquivalence"))]));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula DependentSum(
        Formula variable, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(variable, Colon, Sp, type), Sp, body);

    private static Formula Inverse(Formula equivalence) =>
        Seq(equivalence, Caret, Grp(Minus, D(1)));

    private static Formula AdmissibleFiberFormula()
    {
        Formula source = F.Id("X");
        Formula coordinateType = F.Id("B");
        Formula readout = F.Id("q");
        Formula admissible = F.Id("Adm");
        Formula coordinate = F.Id("b");
        Formula point = F.Id("x");
        Formula proposition = Seq(Operatorname, Grp(F.Id("Prop")));
        Formula fiber = Call("AdmissibleConceptFiber", readout, admissible, coordinate);
        Formula body = Grp(
            Apply(admissible, point), Sp, Land, Sp,
            Apply(readout, point), Sp, Eq, Sp, coordinate);

        return Disp(Seq(
            Forall, Sp, source, Comma, Sp, coordinateType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            readout, Colon, Sp, Arrow(source, coordinateType), Comma, Sp,
            admissible, Colon, Sp, Arrow(source, proposition),
            Comma, Sp, coordinate, Colon, Sp, coordinateType, Comma, Sp,
            fiber, Sp, Eq, Sp, DependentSum(point, source, body), Dot));
    }

    private static Formula DecompositionFormula()
    {
        Formula source = F.Id("X");
        Formula coordinateType = F.Id("B");
        Formula readout = F.Id("q");
        Formula admissible = F.Id("Adm");
        Formula coordinate = F.Id("b");
        Formula point = F.Id("x");
        Formula evidence = F.Id("h");
        Formula path = F.Id("p");
        Formula ordinary = F.Id("e");
        Formula restricted = Subscript(F.Id("e"), admissible);
        Formula ordinaryFiber = Call("ConceptFiber", readout, coordinate);
        Formula restrictedFiber =
            Call("AdmissibleConceptFiber", readout, admissible, coordinate);
        Formula ordinarySum = DependentSum(coordinate, coordinateType, ordinaryFiber);
        Formula restrictedDomain =
            DependentSum(point, source, Apply(admissible, point));
        Formula restrictedSum =
            DependentSum(coordinate, coordinateType, restrictedFiber);

        Formula ordinaryForward = Seq(
            Forall, Sp, point, Colon, Sp, source, Comma, Sp,
            Apply(ordinary, point), Sp, Eq, Sp,
            Langle, Sp, Apply(readout, point), Comma, Sp,
            Langle, Sp, point, Comma, Sp, F.Id("refl"), Sp, Rangle, Sp, Rangle);
        Formula ordinaryBackward = Seq(
            Forall, Sp, coordinate, Colon, Sp, coordinateType, Comma, Sp,
            point, Colon, Sp, source, Comma, Sp,
            path, Colon, Sp, Apply(readout, point), Sp, Eq, Sp, coordinate, Comma, Sp,
            Apply(Inverse(ordinary), Seq(Langle, Sp, coordinate, Comma, Sp,
                Langle, Sp, point, Comma, Sp, path, Sp, Rangle, Sp, Rangle)),
            Sp, Eq, Sp, point);
        Formula ordinaryClause = Seq(
            Exists, Bang, Sp, ordinary, Colon, Sp,
            source, Sp, Equiv, Sp, ordinarySum, Comma, Sp,
            Grp(ordinaryForward), Sp, Land, Sp, Grp(ordinaryBackward));

        Formula restrictedForward = Seq(
            Forall, Sp, point, Colon, Sp, source, Comma, Sp,
            evidence, Colon, Sp, Apply(admissible, point), Comma, Sp,
            Apply(restricted, Seq(Langle, Sp, point, Comma, Sp, evidence, Sp, Rangle)),
            Sp, Eq, Sp,
            Langle, Sp, Apply(readout, point), Comma, Sp,
            Langle, Sp, point, Comma, Sp, evidence, Comma, Sp, F.Id("refl"),
            Sp, Rangle, Sp, Rangle);
        Formula restrictedBackward = Seq(
            Forall, Sp, coordinate, Colon, Sp, coordinateType, Comma, Sp,
            point, Colon, Sp, source, Comma, Sp,
            evidence, Colon, Sp, Apply(admissible, point), Comma, Sp,
            path, Colon, Sp, Apply(readout, point), Sp, Eq, Sp, coordinate, Comma, Sp,
            Apply(Inverse(restricted), Seq(Langle, Sp, coordinate, Comma, Sp,
                Langle, Sp, point, Comma, Sp, evidence, Comma, Sp, path,
                Sp, Rangle, Sp, Rangle)),
            Sp, Eq, Sp, Langle, Sp, point, Comma, Sp, evidence, Sp, Rangle);
        Formula restrictedClause = Seq(
            Exists, Bang, Sp, restricted, Colon, Sp,
            restrictedDomain, Sp, Equiv, Sp, restrictedSum, Comma, Sp,
            Grp(restrictedForward), Sp, Land, Sp, Grp(restrictedBackward));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, source, Comma, Sp, coordinateType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            readout, Colon, Sp, Arrow(source, coordinateType), Comma, Sp,
            admissible, Colon, Sp,
            Arrow(source, Seq(Operatorname, Grp(F.Id("Prop")))),
            Comma, RowBreak, Grp(),
            Grp(ordinaryClause), Sp, Land, RowBreak, Grp(),
            Grp(restrictedClause), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
