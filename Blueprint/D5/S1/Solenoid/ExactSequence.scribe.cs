using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid;

internal sealed class ExactSequenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create("Compatible congruence data form exactly the kernel of the solenoid phase projection.",
H("The Solenoid Exact Sequence"),
Blocks(
                Describe.Lean(
                    DescribeId.Create("compatible-congruence-data-form-the-projection-kernel"),
                    DeclarationHandle.Create("D5/S1/Solenoid/ExactSequence."
                        + "congruence_solenoid_short_exact"),
                    H("Congruence data are exactly the invisible fiber"),
                    StatementSource.FromAuthor(Disp(Seq(
                        D(0), Sp, To, Sp, F.Id("CongruenceData"), Sp, To, Sp,
                        F.Id("UniversalSolenoid"), Sp, To, Sp,
                        F.Id("UnitAddCircle"), Sp, To, Sp, D(0), Comma, Sp,
                        Operatorname, Grp(F.Id("exact"))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "A compatible residue at each positive modulus enters the corresponding "
                            + "circle coordinate through the canonical finite-torsion embedding. "
                            + "Compatibility makes these coordinates a solenoid element whose visible "
                            + "phase is zero. Conversely, every element with zero visible phase is "
                            + "torsion in each coordinate; choosing its unique finite residue and using "
                            + "coordinate compatibility reconstructs the congruence family. The "
                            + "inclusion is injective, its range is exactly the projection kernel, and "
                            + "the visible projection is surjective.")),
                        Paragraph(Text(
                            "The pinned library was searched before construction. It supplies "
                            + "Function.Exact, ZMod.toAddCircle, ZMod.toAddCircle_injective, and "
                            + "AddCircle.nsmul_eq_zero_iff, but contains no solenoid definition or "
                            + "profinite-kernel exact sequence. This result is a new assembly from those "
                            + "library primitives rather than a thin wrapper. The source atom explicitly "
                            + "leaves its topological duality layer open; this theorem claims only the "
                            + "element-level exact sequence."))),
                    DescribeRole.Theorem)),
[
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S1/Dynamics/UniversalSolenoid")),
            ]));
}
