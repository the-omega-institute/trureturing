using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedBirthEnumerationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedBirthEnumeration.";
    private static Formula V(string x) => F.Id(x);
    private static Formula All(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula Ex(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula CH => Eq(Call("continuum", V("UniverseZero")), V("alephOne"));
    private static Formula Onto(string f, Formula type) => Ex(f, type, Call("Surjective", V(f)));
    private static Formula Coding() => Disp(All("X", V("TypeU"),
        All("m", Call("MeasurableSpace", V("X")),
            Imp(Call("CountablyGenerated", V("X"), V("m")),
                Call("Le", Call("CardinalMk", Arr(V("Nat"), Call("SignedMeasure", V("X"), V("m")))),
                    Call("continuum", V("UniverseU")))))));
    private static Formula Signed() => Disp(All("X", V("TypeOne"),
        All("top", Call("TopologicalSpace", V("X")),
            Imp(Call("PseudoMetrizableSpace", V("X"), V("top")),
            Imp(Call("CompactSpace", V("X"), V("top")),
                All("m", Call("MeasurableSpace", V("X")),
                    Imp(Call("BorelSpace", V("X"), V("top"), V("m")),
                    Imp(Call("SecondCountableTopology", V("X"), V("top")),
                        All("V", Call("SupportFamily", V("X"), V("top")), Imp(CH,
                            Onto("nu", Arr(V("Label"),
                                Call("BornData", V("X"), V("top"), V("m"), V("V"))))))))))))));
    private static Formula Supports() => Disp(All("X", V("TypeU"),
        All("top", Call("TopologicalSpace", V("X")),
            All("p", Call("ContinuousMap", V("X"), V("top"), Call("Cube", V("omega"))),
                Imp(Call("Surjective", V("p")),
                    Call("Nonempty", Call("SupportFamily", V("X"), V("top"))))))));
    private static Formula Clopens() => Disp(All("X", V("TypeOne"),
        All("top", Call("TopologicalSpace", V("X")),
            Imp(Call("CompactSpace", V("X"), V("top")),
            Imp(Call("T2Space", V("X"), V("top")),
            Imp(Call("TotallyDisconnectedSpace", V("X"), V("top")),
            Imp(Call("SecondCountableTopology", V("X"), V("top")),
                All("p", Call("ContinuousMap", V("X"), V("top"), Call("Cube", V("omega"))),
                    Imp(Call("Surjective", V("p")), Imp(CH,
                        And(Onto("U", Arr(V("Label"), Call("SupportFamily", V("X"), V("top")))),
                            Onto("P", Arr(V("Nat"), Call("Clopens", V("X"), V("top")))))))))))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual legal signed births and exhaustive proper-stage enumerations under the continuum hypothesis.",
        H("Signed birth enumeration"), Blocks(
            Paragraph(Text(
                "The variables top and m range over the indicated topological and measurable structures on X. "
                + "SupportFamily(X) consists of a Nat-indexed sequence of clopen sets, nonempty at every index, "
                + "with pairwise disjoint underlying sets. BornData(V) is the exact subtype of sequences of actual "
                + "RegularSigned(X) measures whose total variation on the whole space is one, whose total variation "
                + "on the complement of V(n) is zero, and whose positive Jordan mass on the whole space is at least one half, "
                + "at every n. Both Jordan parts are regular. These are independent certificates; normalization alone "
                + "does not imply support nullity or positive mass. Label is exactly SignedProperLimit.Label. "
                + "Every enumerated value is a legal signed sequence, including labels not yet eligible for bookkeeping.")),
            Describe.Lean(DescribeId.Create("countably-generated-signed-sequence-bound"),
                DeclarationHandle.Create(Owner + "signed_sequences_card_le_continuum"),
                H("Countable-generator signed coding"), StatementSource.FromAuthor(Coding()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any countably generated measurable space, signedCode evaluates a real signed measure on finite "
                    + "intersections of natGeneratingSequence. The empty intersection is the whole space. "
                    + "VectorMeasure.ext_of_generateFrom on the existing finite-intersection pi-system proves injectivity. "
                    + "A sequence of measures is then coded by reals indexed by Nat times Finset(Nat). "
                    + "This countable index has real-function cardinal continuum. No regularity, normalization, positivity, "
                    + "compactness or signed representation theorem is required for this bound."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("legal-signed-birth-enumeration"),
                DeclarationHandle.Create(Owner + "exists_signed_enumeration"),
                H("Total exhaustive signed enumeration"), StatementSource.FromAuthor(Signed()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let X live in Type1 with a compact pseudometrizable second-countable topology and its Borel measurable space. "
                    + "For every SupportFamily V, CH in Universe0 gives a surjection Label to BornData(V). "
                    + "Nonemptiness is proved by choosing a point in each support and taking the Jordan pair (dirac,zero). "
                    + "The Jordan conversion theorem identifies the actual positive and negative parts; their sum is dirac. "
                    + "Regularity follows on the proper compact pseudometrizable Borel carrier. "
                    + "The countable-generator code bounds the entire legal subtype, and explicit cardinal lifts align CH with Label. "
                    + "The embedding-to-surjection theorem uses this actual nonempty codomain. No optional value fills a measure entry."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("base-cube-supplies-legal-supports"),
                DeclarationHandle.Create(Owner + "exists_supportFamily"),
                H("Legal supports from an onto base projection"), StatementSource.FromAuthor(Supports()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Any topological space with an actual continuous surjection to the literal Cube(omega) has a SupportFamily. "
                    + "The nth base cylinder has coordinate n true and every preceding natural coordinate false. "
                    + "Finite intersections make it clopen; the single-true-coordinate point proves nonemptiness; "
                    + "the earlier true coordinate contradicts membership in a later cylinder. "
                    + "SupportFamily.pullback uses the given continuous map literally, preserving each index, clopenness "
                    + "and disjointness; surjectivity preserves nonemptiness. The same operation transports an already "
                    + "enumerated family to its actual launch carrier."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exhaustive-clopen-birth-enumerations"),
                DeclarationHandle.Create(Owner + "exists_clopen_enumerations"),
                H("Exhaustive support families and clopens"), StatementSource.FromAuthor(Clopens()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a compact Hausdorff totally disconnected second-countable Type1 carrier with an onto base projection, "
                    + "CH gives a surjection Label to all SupportFamily values and a surjection Nat to all clopens. "
                    + "The existing Clopens.countable_iff_secondCountable theorem supplies countability. "
                    + "Countable sequences of clopens have cardinal at most continuum, and the actual base pullback supplies "
                    + "a legal value. These are proper-stage birth constructions. They neither construct the global history "
                    + "nor impose metrizability or subsequence bookkeeping on the final omegaOne space."))), DescribeRole.Theorem))));
}
