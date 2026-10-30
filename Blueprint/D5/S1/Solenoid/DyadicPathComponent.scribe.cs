using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid;

internal sealed class DyadicPathComponentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two points of the actual dyadic solenoid are joined exactly when a unique real-flow time translates one to the other.",
        H("Dyadic Solenoid Path Components and Unique Time"),
        Blocks(
            Paragraph(Text(
                "S2 is the existing DyadicSolenoid: compatible sequences of unit additive-circle coordinates with 2 x(n+1)=x(n), "
                + "with the inherited product subspace topology. The actual additive map j=realFlow has coordinate j(t)(n)=t/2^n modulo one. "
                + "This is the doubling inverse limit, distinct from the all-positive-degree UniversalSolenoid; no change of carrier or topology is made.")),
            Describe.Lean(
                DescribeId.Create("dyadic-path-orbit-classification"),
                DeclarationHandle.Create("D5/S1/Solenoid/DyadicPathComponent.dyadic_path_orbit_classification"),
                H("A unique real translation characterizes being joined"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Sp, InMacro, Sp, F.Id("S2"), Comma, Esc,
                    Operatorname, Grp(F.Id("Joined")), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                    Sp, Iff, Sp, Exists, Bang, Sp, F.Id("t"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Esc,
                    F.Id("y"), Sp, Eq, Sp, F.Id("j"), Open, F.Id("t"), Close, Sp, Plus, Sp, F.Id("x")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every x and y in S2, Joined x y holds if and only if there is exactly one real t with y=j(t)+x. "
                        + "Thus the real translation action is free and its orbits are precisely the path components. Uniqueness concerns the endpoint time, "
                        + "not the parametrization of the path.")),
                    Paragraph(Text(
                        "Translate a path from x to y by subtracting x. Lift its zeroth circle coordinate through the covering from the real line to the unit circle, "
                        + "with initial lift zero. Write the continuous real lift as a. Dyadic compatibility gives 2^n times coordinate n equal to coordinate zero. "
                        + "Both coordinate n of the translated path and the circle class of a/2^n lift that same coordinate-zero path through multiplication by 2^n. "
                        + "They agree initially, so covering-lift uniqueness on the connected unit interval identifies them everywhere. The endpoint is j(a(1)). "
                        + "Conversely u maps to j(u t)+x along the unit interval and is an explicit path.")),
                    Paragraph(Text(
                        "Injectivity follows directly from the dyadic coordinates. If j(t)=0, choose n with 2^n greater than the absolute value of t. "
                        + "Coordinate n says that t/2^n is an integer. Its absolute value is less than one, so it is zero and hence t=0. "
                        + "The additive kernel criterion makes j injective; cancellation supplies uniqueness of t. "
                        + "The local coordinate induction and kernel argument are consumed helpers, while the new construction is the identification of arbitrary dyadic paths.")),
                    Paragraph(Text(
                        "Let h be the parent's alternating order-three point thirdPoint. If a path joined zero to h, the classification would give h=j(t). "
                        + "Then r maps to j(t r) would be a continuous additive real homomorphism taking 1 to h, contradicting the parent's real-time obstruction. "
                        + "Consequently S2 is connected but is not path connected. The parent's algebraic rational homomorphism taking 1 to h is discontinuous "
                        + "and does not supply a path or a continuous real action through h.")),
                    Paragraph(Text(
                        "The proof reuses the pinned Mathlib covering, path-lifting, unbounded-power and additive-circle APIs and the repository's dyadic construction. "
                        + "The covering technique also occurs in StreamlineDecomposition for the different all-degree carrier. "
                        + "These are classical solenoid phenomena; no literature novelty or physical realization is asserted."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Solenoid/DyadicTimeSeparation")),
        ]));
}
