using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;
internal sealed class FiniteCausalPortGraphDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Disjoint quantum ports and topological-order independence",H("Disjoint quantum ports and topological-order independence"),
        Blocks(Describe.Lean(DescribeId.Create("disjoint-port-interchange"),
            DeclarationHandle.Create("D5/S3/Quantum/Dynamics/FiniteCausalPortGraph.disjoint_port_interchange"),
            H("Actual disjoint Kraus ports interchange on correlated matrices"),StatementSource.FromAuthor(Disp(All("I",Call("Type"),All("J",Call("Type"),All("O",Call("Type"),All("P",Call("Type"),All("M",Call("Type"),All("N",Call("Type"),Instance(Call("Fintype",F.Id("I")),Instance(Call("DecidableEq",F.Id("I")),Instance(Call("Fintype",F.Id("J")),Instance(Call("DecidableEq",F.Id("J")),Instance(Call("Fintype",F.Id("O")),Instance(Call("DecidableEq",F.Id("O")),Instance(Call("Fintype",F.Id("P")),Instance(Call("DecidableEq",F.Id("P")),Instance(Call("Fintype",F.Id("M")),Instance(Call("Fintype",F.Id("N")),All("A",Call("KrausFamily",F.Id("M"),F.Id("O"),F.Id("I")),All("B",Call("KrausFamily",F.Id("N"),F.Id("P"),F.Id("J")),All("rho",Call("State",Call("Product",F.Id("I"),F.Id("J"))),Rel(Call("rightBranch",F.Id("B"),Call("leftBranch",F.Id("A"),F.Id("rho"))),Eq,Call("leftBranch",F.Id("A"),Call("rightBranch",F.Id("B"),F.Id("rho"))))))))))))))))))))))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/chiribella2009networks")),
            Blocks(Paragraph(Text("The two branches act as A tensor identity and identity tensor B on the full joint matrix. Rectangular Kronecker multiplication identifies either composed Kraus operator with A tensor B. Interchanging the finite hidden-label sums then proves the equality without requiring a product input or assuming commutation."))),DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("quantum-port-interchange"),
            DeclarationHandle.Create("D5/S3/Quantum/Dynamics/FiniteCausalPortGraph.quantum_schedule_independence"),H("Disjoint quantum ports and topological-order independence"),
            StatementSource.FromAuthor(Disp(All("E",Call("Type"),Instance(Call("PartialOrder",F.Id("E")),All("G",Call("QuantumPortGraph",F.Id("E")),All("h",Call("Records",Call("Outcomes",F.Id("G"))),All("K",Call("Set",F.Id("E")),All("L",Call("Set",F.Id("E")),All("l",Call("List",F.Id("E")),All("m",Call("List",F.Id("E")),All("X",Call("State",Call("Cut",F.Id("G"),F.Id("K"))),Rel(Conj(Call("IsLowerSet",F.Id("K")),Call("IsLowerSet",F.Id("L")),Call("Finite",F.Id("L")),Call("Exec",F.Id("K"),F.Id("l"),F.Id("L")),Call("Exec",F.Id("K"),F.Id("m"),F.Id("L"))),Implies,Rel(Call("pathMap",Call("Readout",F.Id("G"),F.Id("h")),F.Id("l"),F.Id("X")),Eq,Call("pathMap",Call("Readout",F.Id("G"),F.Id("h")),F.Id("m"),F.Id("X"))))))))))))))),AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/chiribella2009networks")),
            Blocks(Paragraph(Text("Every cut has a finite complex matrix interface. A local instrument has finitely many actual outcomes and hidden Kraus labels, rectangular Kraus matrices, and sum over outcomes and hidden labels of K-adjoint K equal to identity. Its combined channel is the canonical FiniteKrausChannel supplier. Branch matrices are actual sums K X K-adjoint, not abstract state-transforming functions. Cut matrices include joint correlations, reference systems, observers, memories and every environment that can interact again.")),
                Paragraph(Text("Acting on one tensor port uses K tensor identity on the complete joint matrix. Rectangular Kronecker multiplication and exchanging the two finite hidden sums show that two disjoint local operations commute on every matrix, including entangled inputs. PortSquare certifies the individual four edge maps as the two corresponding spectator lifts in explicit tensor coordinates. It supplies neither a diamond equation nor a whole-path interchange law. The diamond is derived from these actual quantum interfaces.")),
                Paragraph(Text("An event chooses its Kraus instrument only from the already available record and its own actual outcome. The derived local diamonds and ConfigurationPathTransport finite-endpoint path theorem imply equality of the complete cut matrix for any two legal topological schedules and a fixed event-indexed actual record. Projecting to a subsystem or an effect preserves that equality. The literal occurrence history is not deleted or identified with the output matrix."))),DescribeRole.Theorem))));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Rel(Formula left, Formula relation, Formula right) =>
        Seq(Open, left, Sp, relation, Sp, right, Close);
    private static Formula Conj(params Formula[] statements) =>
        statements.Aggregate((left, right) => Rel(left, Land, right));
    private static Formula Instance(Formula instance, Formula body) =>
        Seq(OpenBracket, instance, CloseBracket, Sp, body);
}
