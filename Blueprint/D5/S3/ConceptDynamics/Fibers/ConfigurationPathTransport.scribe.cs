using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Fibers;
internal sealed class ConfigurationPathTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Configuration ideal completion, actual finite edge composition and invertible graph transport.",
        H("Configurations and rooted transport"),
        Blocks(
            Describe.Lean(DescribeId.Create("configuration-ideal-completion"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Fibers/ConfigurationPathTransport.configurationIdealIso"),
                H("Finite configurations form an ideal basis"),
                StatementSource.FromAuthor(Disp(All("E",Call("Type"),Instance(Call("PartialOrder",F.Id("E")),All("C",Call("Predicate",Call("Finset",F.Id("E"))),Rel(Conj(Call("Apply",F.Id("C"),Emptyset),All("e",F.Id("E"),Call("Finite",Call("Iic",F.Id("e"))))),Implies,Call("OrderIsomorphic",Call("Configurations",F.Id("C")),Call("OrderIdeal",Call("FiniteConfigurations",F.Id("C")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/ConceptDynamics/winskel1987eventstructures")),
                Blocks(Paragraph(Text("A configuration is a lower set whose finite subsets are compatible. Each principal predecessor set is finite, while the ambient poset may be infinite. A nonempty directed family has a compatible lower union: every finite test set lies in one member by finite induction on directedness. The finite subconfigurations of any configuration are nonempty, lower closed and directed. Their union is the configuration because each event lies in its finite principal predecessor set. An ideal is sent to its union; any finite subconfiguration of that union belongs to the ideal by a finite upper-bound argument. These constructions are inverse and preserve inclusion. Empty compatibility supplies the bottom finite configuration."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finite-history-clocks"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Fibers/ConfigurationPathTransport.finite_history_clocks"),
                H("Positive histories and finite observer clocks"),
                StatementSource.FromAuthor(Disp(All("E",Call("Type"),Instance(Call("PartialOrder",F.Id("E")),All("C",Call("Finset",F.Id("E")),All("D",Call("Finset",F.Id("E")),All("B",Call("Finset",F.Id("E")),All("o",Call("Predicate",F.Id("E")),All("w",Call("Function",F.Id("E"),Call("Real")),Rel(Conj(Call("IsLowerSet",F.Id("C")),Call("IsLowerSet",F.Id("D")),Rel(F.Id("C"),Subseteq,F.Id("D")),Rel(F.Id("D"),Subseteq,F.Id("B")),All("e",F.Id("E"),Rel(Call("Apply",F.Id("o"),F.Id("e")),Implies,Rel(D(0),Lt,Call("Apply",F.Id("w"),F.Id("e")))))),Implies,Ex("l",Call("List",F.Id("E")),Conj(Call("Exec",F.Id("C"),F.Id("l"),F.Id("D")),Rel(Call("Length",F.Id("l")),Eq,Call("gapCard",F.Id("C"),F.Id("D"))),All("m",Call("List",F.Id("E")),Rel(Call("Exec",F.Id("C"),F.Id("m"),F.Id("D")),Implies,Rel(Call("Length",F.Id("m")),Eq,Call("gapCard",F.Id("C"),F.Id("D"))))),Rel(Call("gapCard",F.Id("C"),F.Id("B")),Eq,Rel(Call("gapCard",F.Id("C"),F.Id("D")),Plus,Call("gapCard",F.Id("D"),F.Id("B")))),Rel(Call("clockFinite",F.Id("o"),F.Id("w"),F.Id("C")),Le,Call("clockFinite",F.Id("o"),F.Id("w"),F.Id("D"))),Rel(Ex("e",F.Id("E"),Conj(Call("Member",F.Id("e"),F.Id("D")),Call("NotMember",F.Id("e"),F.Id("C")),Call("Apply",F.Id("o"),F.Id("e")))),Implies,Rel(Call("clockFinite",F.Id("o"),F.Id("w"),F.Id("C")),Lt,Call("clockFinite",F.Id("o"),F.Id("w"),F.Id("D")))),All("m",Call("List",F.Id("E")),Rel(Call("Exec",F.Id("D"),F.Id("m"),F.Id("C")),Implies,Rel(F.Id("l"),Eq,Call("Nil")))),All("e",F.Id("E"),All("p",Call("List",F.Id("E")),All("s",Call("List",F.Id("E")),Rel(Rel(Call("pathWeight",F.Id("w"),Call("Cons",F.Id("e"),F.Id("s"))),Eq,Call("pathWeight",F.Id("w"),Call("Append",F.Id("p"),F.Id("s")))),Iff,Rel(Call("Apply",F.Id("w"),F.Id("e")),Eq,Call("pathWeight",F.Id("w"),F.Id("p"))))))))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For C contained in D contained in B, the actual basic-edge schedule from C to D exists and has exactly |D minus C| steps. Every legal path with those endpoints has this same length. These gap cardinalities add across the nested triple. The finite observer clock sums only observed events with strictly positive weights: inclusion cannot decrease it, and any newly observed event makes it strictly larger. If a reverse execution from D to C exists, the forward history is empty. Replacing one event by a list of pieces preserves duration exactly when the original weight equals the sum of the piece weights. No infinite configuration sum is asserted to be a finite real number."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("local-edge-diamonds"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Fibers/ConfigurationPathTransport.pathIndependent_iff_diamondCompatible"),
                H("Actual edge diamonds determine finite path composites"),
                StatementSource.FromAuthor(Disp(All("E",Call("Type"),Instance(Call("PartialOrder",F.Id("E")),All("R",Call("DependentReadout",F.Id("E")),Rel(Call("PathIndependent",F.Id("R")),Iff,Call("DiamondCompatible",F.Id("R")))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The path map is recursively the composite of actual edge maps. The diamond hypothesis concerns only the two legal edge composites, without an assumed surrounding-path interchange. At finite endpoints the frozen EnabledPathSwapConnectivity theorem is applied to the finite endpoint subtype, then lifted back to the arbitrary ambient poset. Adjacent incomparable swaps connect all legal schedules. Equality on each local diamond therefore propagates through prefixes and suffixes. Conversely the two length-two paths give each diamond. ConfigurationReadout restricts this result faithfully to the original fibres defined only at legal configurations."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("root-fixed-points"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Fibers/ConfigurationPathTransport.rootSectionMap_bijective"),
                H("Parallel sections correspond to closed-walk fixed points"),
                StatementSource.FromAuthor(Disp(All("V",Call("Type"),All("G",Call("BiGraph",F.Id("V")),All("F",Call("Function",F.Id("V"),Call("Type")),All("T",Call("EdgeTransport",F.Id("G"),F.Id("F")),All("r",F.Id("V"),Rel(Call("GraphConnectedFrom",F.Id("G"),F.Id("r")),Implies,Call("Bijective",Call("rootSectionMap",F.Id("T"),F.Id("r"))))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Walk transports are constructed recursively from bijective oriented edge maps; reversal uses the given inverse edge maps, and concatenation follows by induction. A root point fixed by every closed walk transports consistently to a parallel section along chosen root paths. Comparing two paths forms a closed walk and proves independence. Evaluation at the root is the inverse map. No claim that a loop operator is the identity is needed: it must fix the chosen root point."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tree-coordinate-trivialization"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Fibers/ConfigurationPathTransport.tree_coordinate_trivialization"),
                H("Tree coordinates make the reversible edge maps identity"),
                StatementSource.FromAuthor(Disp(All("V",Call("Type"),All("G",Call("SimpleGraph",F.Id("V")),All("F",Call("Function",F.Id("V"),Call("Type")),All("r",F.Id("V"),All("e",Call("EdgeEquivalences",F.Id("G"),F.Id("F")),Rel(Conj(Call("IsTree",F.Id("G")),Call("ReverseIsInverse",F.Id("G"),F.Id("e"))),Implies,Ex("c",Call("RootFibreCoordinates",F.Id("F"),F.Id("r")),All("v",F.Id("V"),All("w",F.Id("V"),Rel(Call("Adjacent",F.Id("G"),F.Id("v"),F.Id("w")),Implies,Rel(Call("Compose",Call("Apply",F.Id("c"),F.Id("v")),Call("Apply",F.Id("e"),F.Id("v"),F.Id("w")),Call("Inverse",Call("Apply",F.Id("c"),F.Id("w")))),Eq,Call("Identity",Call("Apply",F.Id("F"),F.Id("r")))))))))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The unique simple root path gives the fibre coordinate at every vertex. Tree path uniqueness and edge reversal imply that every transported edge is the identity on the root fibre. The original walk and every literal edge occurrence are unchanged by this coordinate construction. Inverse transport is an algebraic operation on fibre values; it is not a deletion edge in the positive history relation."))),
                DescribeRole.Theorem))));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Open, Exists, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Rel(Formula left, Formula relation, Formula right) =>
        Seq(Open, left, Sp, relation, Sp, right, Close);
    private static Formula Conj(params Formula[] statements) =>
        statements.Aggregate((left, right) => Rel(left, Land, right));
    private static Formula Instance(Formula instance, Formula body) =>
        Seq(OpenBracket, instance, CloseBracket, Sp, body);
}
