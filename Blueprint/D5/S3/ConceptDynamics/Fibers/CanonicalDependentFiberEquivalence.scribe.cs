using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Fibers;

internal sealed class CanonicalDependentFiberEquivalenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical dependent-fiber equivalence records a readout and recovers its source.",
        H("Canonical Dependent Fiber Equivalence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("canonical-dependent-fiber-equivalence"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Fibers/CanonicalDependentFiberEquivalence."
                        + "whole_dependent_fiber_form"),
                H("Canonical dependent-fiber equivalence"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any readout q : X -> B, the named equivalence e_q sends x to "
                            + "its coordinate q(x), the same object x, and the reflexive "
                            + "proof that x lies in that fiber.")),
                    Paragraph(Text(
                        "The inverse computation is public as well: it recovers x by "
                            + "forgetting the coordinate and equality witness.")),
                    Paragraph(Text(
                        "No quotient, surjectivity, section, linear structure, or metric is "
                            + "assumed. The construction uses the pinned natural fiber "
                            + "equivalence directly, and its axiom audit has no choice dependency."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula source = F.Id("X");
        Formula coordinateType = F.Id("B");
        Formula coordinate = F.Id("b");
        Formula point = F.Id("x");
        Formula proof = F.Id("p");
        Formula readout = F.Id("q");
        Formula equivalence = Seq(F.Id("e"), Underscore, Grp(readout));
        Formula sigma = Seq(Sum, Sp, Underscore,
            Grp(coordinate, Colon, Sp, coordinateType), Sp,
            Call("ConceptFiber", readout, coordinate));
        Formula forwardValue = Seq(
            Langle, Sp, Apply(readout, point), Comma, Sp,
            Langle, Sp, point, Comma, Sp, F.Id("refl"), Rangle, Rangle);
        Formula fiberValue = Seq(
            Langle, Sp, coordinate, Comma, Sp,
            Langle, Sp, point, Comma, Sp, proof, Rangle, Rangle);
        Formula inverse = Seq(equivalence, Caret, Grp(Minus, D(1)));

        return Disp(Seq(
            Forall, Sp, source, Comma, Sp, coordinateType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            readout, Colon, Sp, source, Sp, To, Sp, coordinateType, Comma, Sp,
            equivalence, Sp, Colon, Eq, Sp,
            Operatorname, Grp(F.Id("canonical")), Open, readout, Close,
            Colon, Sp, source, Sp, Equiv, Sp, sigma, Comma, Sp,
            Open,
            Forall, Sp, point, Colon, Sp, source, Comma, Sp,
            Apply(equivalence, point), Sp, Eq, Sp, forwardValue,
            Close, Sp, Land, Sp,
            Open,
            Forall, Sp, coordinate, Colon, Sp, coordinateType, Comma, Sp,
            point, Colon, Sp, source, Comma, Sp,
            proof, Colon, Sp, Apply(readout, point), Sp, Eq, Sp, coordinate,
            Comma, Sp, Apply(inverse, fiberValue), Sp, Eq, Sp, point,
            Close, Dot));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);
}
