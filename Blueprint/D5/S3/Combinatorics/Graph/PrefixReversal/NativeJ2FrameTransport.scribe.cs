using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeJ2FrameTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual label relabelling earns arbitrary two-selected-label frame domains and all literal J2 ports without changing barred indices.",
        H("Arbitrary Native J2 Frame Identification"),
        Blocks(
            Definition("relabel", "Actual Left Label Relabelling", Eq(Rho(),
                Mul(Call("anchor", F.Id("F")), Call("Inverse", RawRight(D(0))))),
                "rho is anchor(F) times the inverse of the independently specified native R0. It acts by left multiplication on configurations, so every native position generator remains the same."),
            Definition("reverseSelected", "Reverse Only the Two Selected Labels", Call("reverseSelected", F.Id("F")),
                "The reversed frame uses selected.reverse with exactly the original base and terminal. Its full nodup and complete-label obligations are earned from the original frame. This operation does not reverse the base or rename indices one and two."),
            Definition("frameDomainIso", "Actual Native Graph Isomorphism", Call("frameDomainIso", F.Id("m"), F.Id("F")),
                "For m at least five, left multiplication by rho is a graph isomorphism from the complete fixed F2 native domain to Layer(selected.toFinset, terminal :: base). Its vertex bijection follows from the earned full layer identification; its adjacency equivalence is the existing Cayley left-translation theorem."),
            Theorem("native_j2_frame_domain_iff", "Every Actual Vertex Has the Independent Frame Domain", DomainFormula(),
                "For every m at least five and every SupplyFrame(m,2), a configuration rho*x lies in Layer(selected.toFinset, terminal :: base) exactly when x belongs to the independent F2Domain. The conclusion concerns every actual configuration, not only suppliers, ports, or one candidate walk. The proof transports deletion through an injective label map, identifies the erased actual anchor, and reuses the complete F2 layer theorem. No domain equivalence is a premise."),
            Theorem("native_j2_frame_ports", "All Original Unbarred Indices Are Preserved", PortsFormula(false),
                "The same rho takes each original native R_i and L_i, for i in Fin(3), to the literal rightPort(F,i) and leftPort(F,i). The proof earns R_i = R0*(bc)^i from actual permutation values, then cancels the original anchor inverse. No endpoint correspondence is supplied as a premise."),
            Theorem("native_j2_frame_barred_ports", "Barred Ports Use the Reversed Selected Frame at the Same Index", PortsFormula(true),
                "The same rho takes bar R_i and bar L_i to rightPort(reverseSelected(F),i) and leftPort(reverseSelected(F),i), at the original index i. The label transposition acts only on the two selected labels because the full tuple is nodup. Thus a later actual half-restoration consumer keeps the literal barred exception R0 to R1, L1 to R2 and L2 to L0. This identification does not supply a prior-cycle edge inventory or prove the all-size recursive Hamilton-cycle conclusion."))));

    private static DocumentBlock Definition(string selector, string title, Formula formula, string meaning) =>
        Describe.Lean(DescribeId.Create(selector.ToLowerInvariant()), DeclarationHandle.Create(Prefix + selector),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(meaning))), DescribeRole.Definition);
    private static DocumentBlock Theorem(string selector, string title, Formula formula, string meaning) =>
        Describe.Lean(DescribeId.Create(selector.Replace('_', '-')), DeclarationHandle.Create(Prefix + selector),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(meaning))), DescribeRole.Theorem);
    private static Formula Rho() => Call("relabel", F.Id("F"));
    private static Formula Mul(Formula x, Formula y) => Call("Multiply", x, y);
    private static Formula RawRight(Formula i) => Call("NativeRightPort", F.Id("m"), i);
    private static Formula RawLeft(Formula i) => Call("NativeLeftPort", F.Id("m"), i);
    private static Formula DomainFormula()
    {
        Formula m = F.Id("m"), x = F.Id("x"), frame = F.Id("F");
        return Disp(All("m", Call("Nat"), Implies(Le(D(5), m),
            All("F", Call("SupplyFrame", m, D(2)), All("x", Call("Configuration", m),
                Iff(Call("Layer", Call("ToFinset", Call("Selected", frame)),
                    Call("CycleOfList", Call("Cons", Call("Terminal", frame), Call("Base", frame))),
                    Mul(Rho(), x)), Call("F2Domain", m, x)))))));
    }
    private static Formula PortsFormula(bool barred)
    {
        Formula m = F.Id("m"), i = F.Id("i"), frame = F.Id("F");
        Formula supplied = barred ? Call("reverseSelected", frame) : frame;
        Formula right = barred ? Call("NativeBar", RawRight(i)) : RawRight(i);
        Formula left = barred ? Call("NativeBar", RawLeft(i)) : RawLeft(i);
        return Disp(All("m", Call("Nat"), Implies(Le(D(5), m),
            All("F", Call("SupplyFrame", m, D(2)), All("i", Call("Fin", D(3)),
                And(Eq(Mul(Rho(), right), Call("rightPort", supplied, Call("FinValue", i))),
                    Eq(Mul(Rho(), left), Call("leftPort", supplied, Call("FinValue", i)))))))));
    }
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
}
