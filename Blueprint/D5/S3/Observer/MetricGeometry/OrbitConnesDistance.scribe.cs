using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometry;

internal sealed class OrbitConnesDistanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded observables with unit one-step update defect recover the exact distance on the free integer shift orbit.",
        H("Observable-Supremum Distance on the Integer Orbit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("admissible-observables-have-unit-one-step-update-defect"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/OrbitConnesDistance."
                        + "orbitLipBall_unit_update_defect"),
                H("Admissible observables have unit one-step update defect"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("f"), Sp, InMacro, Sp,
                    F.Id("B"), Underscore, Grp(F.Id("L")), Comma, Esc,
                    Forall, Sp, F.Id("k"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Esc,
                    Vert, Sp,
                    F.Id("f"), Open, F.Id("k"), Plus, D(1), Close,
                    Minus, Sp, F.Id("f"), Open, F.Id("k"), Close,
                    Vert, Sp, Leq, Sp, D(1), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let the admissible ball consist of bounded real functions on the integer "
                        + "orbit whose complexified observable has frozen read-update defect norm "
                        + "at most one at every coordinate. Evaluating that defect at the successor "
                        + "coordinate gives an adjacent real value change of at most one. Telescoping those "
                        + "adjacent bounds later supplies the global Lipschitz estimate used by "
                        + "the distance theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-observable-supremum-equals-the-integer-orbit-distance"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/OrbitConnesDistance."
                        + "orbit_connes_distance_eq"),
                H("The observable supremum equals the integer orbit distance"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("m"), Comma, Sp, F.Id("n"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("Z")), Comma, Esc,
                    F.Id("d"), Underscore, Grp(F.Id("L")), Open,
                    F.Id("m"), Comma, Sp, F.Id("n"), Close,
                    Sp, Eq, Sp,
                    Vert, Sp, F.Id("m"), Minus, Sp, F.Id("n"), Vert, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Define the distance between two integer orbit points as the real supremum "
                            + "of their value gaps over bounded observables in the unit update-defect "
                            + "ball. Every such gap is at most the ambient integer distance by "
                            + "telescoping adjacent defects in either orbit orientation. The reverse "
                            + "bound is attained by the bounded "
                            + "observable k mapped to the minimum of the distance from k to m and "
                            + "the distance from m to n. The theorem concerns the free integer shift "
                            + "orbit itself, so it retains "
                            + "the absolute-displacement formula without the wrap-around of a "
                            + "finite cyclic quotient. It establishes only the same-orbit metric "
                            + "clause. It does not construct a spectral triple, identify an operator "
                            + "commutator norm, or make bundle, phase-separation, or type-classification "
                            + "claims."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("distance-from-the-orbit-origin-is-absolute-displacement"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/OrbitConnesDistance."
                        + "orbit_distance_from_zero"),
                H("Distance from the orbit origin is absolute displacement"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Esc,
                    F.Id("d"), Underscore, Grp(F.Id("L")), Open,
                    D(0), Comma, Sp, F.Id("n"), Close,
                    Sp, Eq, Sp, Vert, Sp, F.Id("n"), Vert, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Specializing the exact distance theorem to the orbit origin converts the "
                        + "integer metric into the absolute value of the real cast of the integer "
                        + "displacement. Negative and positive shifts therefore have the same "
                        + "distance, while no periodic identification is imposed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-nonconstant-admissible-observable-attains-distance-three"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/OrbitConnesDistance."
                        + "orbit_distance_three_witness"),
                H("A nonconstant admissible observable attains distance three"),
                StatementSource.FromAuthor(Disp(Seq(
                    Exists, Sp, F.Id("f"), Sp, InMacro, Sp,
                    F.Id("B"), Underscore, Grp(F.Id("L")), Comma, Esc,
                    F.Id("f"), Open, D(0), Close,
                    Sp, Neq, Sp, F.Id("f"), Open, D(3), Close,
                    Sp, Land, Sp,
                    Vert, Sp, F.Id("f"), Open, D(0), Close,
                    Minus, Sp, F.Id("f"), Open, D(3), Close, Vert,
                    Sp, Eq, Sp, D(3), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The clipped distance observable based at zero and clipped at three is bounded, "
                        + "belongs to the unit update-defect ball, takes distinct values at zero and "
                        + "three, and has endpoint gap three. This explicit nonconstant witness "
                        + "rules out an empty ball, an all-constant ball, and an identically zero "
                        + "distance."))),
                DescribeRole.Theorem))));
}
