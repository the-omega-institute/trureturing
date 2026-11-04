using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class BalancedMinimalDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimality and an actual balanced Toeplitz generator.",
        H("Minimality and an actual balanced Toeplitz generator"),
        Blocks(
            Describe.Lean(DescribeId.Create("two-block-window"), DeclarationHandle.Create(Owner + "balancedWindow_infix_pair"),
                H("A window meets two blocks"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A length-r window of any actual point lies inside two successive level-n words whenever every level-n word has length at least r. The proof uses the unique marked presentation at the original physical coordinates."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("every-high-block"), DeclarationHandle.Create(Owner + "balancedWindow_infix_block"),
                H("The window occurs in every high block"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every occurring length-r window is an infix of each level-(r+3) balanced word. Equal heights make level r+1 long enough, and the previously proved pair-infix theorem places every ordered pair two levels higher."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-recurrence"), DeclarationHandle.Create(Owner + "balancedWindow_uniform_recurrence"),
                H("A uniform explicit recurrence bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any length-r window of any point, each point and each integer starting position u admit an occurrence starting between u and u+2h(r+3). The next actual high-level boundary supplies a block containing the window. This is a uniform bound across the whole compact intersection."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("common-language"), DeclarationHandle.Create(Owner + "balancedWindow_occurs_everywhere"),
                H("One common finite language"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite consecutive window of one actual point occurs in every other actual point. This follows from the uniform recurrence bound and does not assume minimality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-pattern"), DeclarationHandle.Create(Owner + "balanced_finite_pattern"),
                H("Every finite coordinate pattern is reached"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite set of signed integer coordinates and any two points, an integer shift of the first matches the second on that set. A centered interval containing all specified coordinates reduces the assertion to actual word occurrence."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("dense-orbit"), DeclarationHandle.Create(Owner + "balanced_orbit_dense"),
                H("Every integer orbit is dense"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each integer shift orbit is dense in BalancedPoint. Basic product-open sets constrain only finitely many coordinates, so the finite-pattern theorem supplies an orbit point in every nonempty open set."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("shift-action"), DeclarationHandle.Create(Owner + "balancedShiftAction"),
                H("The integer shift action"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The subtype inherits the actual physical integer shifts as an additive action. The separate balancedShiftMinimal instance records the proved dense-orbit property for this action."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("orbit-closure"), DeclarationHandle.Create(Owner + "balanced_orbit_closure"),
                H("The exact ambient orbit closure"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In the ambient two-sided binary full shift, the closure of the integer orbit of any BalancedPoint is exactly balancedSubshift.carrier. Closed invariance gives one inclusion and subtype orbit density gives the other."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("aligned-membership"), DeclarationHandle.Create(Owner + "alignedPeriodicPoint_mem"),
                H("The aligned point is in this space"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compact aligned-tower point constructed in AlignedTowerLimit belongs to the same actual intersection, since each aligned marked representation is also an ordinary marked representation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("toeplitz-point"), DeclarationHandle.Create(Owner + "exists_balanced_toeplitz_point"),
                H("An actual nonperiodic Toeplitz point"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There is an actual point of this compact intersection with a positive period at each signed coordinate, valid for every positive and negative integer multiple, and with no positive global shift period. This combines aligned coordinate periodicity with the independently proved aperiodicity of every BalancedPoint."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("toeplitz-generator"), DeclarationHandle.Create(Owner + "exists_balanced_toeplitz_generator"),
                H("The point generates the entire subshift"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same binary point has periodic coordinates, no positive global period and ambient integer orbit closure exactly equal to balancedSubshift.carrier. This completes actual Toeplitz generation and minimality. Regular periodic-skeleton density, essential periods, unique ergodicity and lift splitting require separate proofs. The public theorem escape registrations are unfinished under https://github.com/the-omega-institute/trureturing/issues/24726; the current scoped report verifies the Lean declarations and standard axiom closure, and does not constitute declared_validated four-slot audit evidence."))), DescribeRole.Theorem)),
            [ DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift")),
              DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialMinimal")),
              DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/AlignedTowerLimit")) ]));
}
