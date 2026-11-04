using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class FiniteKernelDFAODocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Automata/FiniteKernelDFAO.";
    private static readonly LibraryNoteRef Atlas =
        LibraryNoteRef.Create("D5/L/Automata/atlas2026finitekernel");
    private static readonly LibraryNoteRef Eilenberg =
        LibraryNoteRef.Create("D5/L/Automata/adamczewskibell2012automatic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Over every finite output alphabet, a sequence has finite arithmetic kernel exactly when a finite DFAO computes it on every least-significant-digit-first representation.",
        H("Finite arithmetic kernels and finite output automata"),
        Blocks(
            Paragraph(Text(
                "The characterization is Eilenberg's theorem. Natural indices include zero. A digit word is read least significant digit first; its final digits are the high-order digits.")),
            Node("baseWordValueLSD", "Value of a digit word", ValueFormula(), Atlas,
                "For every natural base k and every finite word ds over Fin k, Value(k,ds) is its least-significant-digit-first value. The right fold starts at zero. Thus the empty word and every all-zero word represent zero; appending high-order zeros preserves value. The notation val(d) denotes the natural value of a digit d.", DescribeRole.Definition),
            Node("IsKAutomaticSequence", "Correctness on every representation", MachineFormula(), Atlas,
                "For a finite output type B, Machine(k,a) requires k at least two and a positive natural state count q, an initial state s, a total transition table t and an output map o. Fold(ds,t,s) is List.foldl: the leftmost, least significant digit is read first. Correctness quantifies over every natural n and every word of value n, including empty and padded representations. Zero-digit transitions are constrained by this output-invariance condition.", DescribeRole.Definition),
            Node("kKernel", "Arithmetic kernel", KernelFormula(), Atlas,
                "For any output type D in any universe, Kernel(k,a) consists of the decimations n ↦ a(k^e n+r), with natural exponent e and residue r less than k^e. No finiteness or additive structure on D is needed to define this set.", DescribeRole.Definition),
            Node("IsKAutomatic", "Finite-kernel automaticity", AutomaticFormula(), Atlas,
                "Automatic(k,a) is the conjunction of k at least two and finiteness of the type of members of Kernel(k,a). This definition is available for arbitrary output types; the equivalence below holds for finite output types B : Type.", DescribeRole.Definition),
            Node("chr_kernel_lam_mem", "One-digit kernel closure", StepFormula(), Atlas,
                "Decimating a kernel element b by a digit j less than q gives another member of the same q-kernel. The construction uses exponent e+1 and residue q^e j+R from a representation of b. This closure supplies the transition of the kernel-state machine.", DescribeRole.Theorem),
            Node("chr_self_mem_kernel", "The original sequence is a kernel state", SelfFormula(), Atlas,
                "The exponent zero and residue zero put every sequence a in its own q-kernel, even for bases zero and one. For the final theorem this state provides the initial state and certifies that the finite state count is positive.", DescribeRole.Theorem),
            Node("isKAutomatic_iff_isKAutomaticSequence", "Eilenberg's finite-kernel equivalence", EquivalenceFormula(), Eilenberg,
                "For every finite B : Type, every natural k and every sequence a : Nat → B, Automatic(k,a) is equivalent to Machine(k,a). Both sides contain the conjunct 2 ≤ k. In the forward direction the states are exactly the kernel elements, relabeled by an equivalence with Fin q; the initial state is a, a digit acts by decimation, and the output is evaluation at zero. The inductive chr_fold_val invariant identifies the reached state with n ↦ b(k^length(ds) n+Value(k,ds)). In the reverse direction, fix a representing word for each n. A kernel element with exponent e and residue r is realized by the state reached after a representing word for r of length exactly e. Padding by high-order zeros supplies that exact length. Concatenating this word with a representing word for n yields k^e n+r, so all kernel elements lie in the finite image of the q states.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        LibraryNoteRef source, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("finite-kernel-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(source), Blocks(Paragraph(Text(prose))), role);

    private static Formula NatType() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Type() => new Formula.NamedConstant(FormulaIdentifier.Create("Type"));
    private static Formula AnyType() => Seq(Type(), Caret, Grp(Star));
    private static Formula FinType(Formula k) => Call("Fin", k);
    private static Formula WordType(Formula k) => Call("List", FinType(k));
    private static Formula Arrow(Formula a, Formula b) => Seq(Open, a, Sp, To, Sp, b, Close);
    private static Formula Sequence(Formula b) => Arrow(NatType(), b);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffOf(Formula a, Formula b) => Seq(Open, a, Sp, Iff, Sp, b, Close);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula Lambda(string name, Formula type, Formula body) => Seq(
        Open, F.Id(name), Colon, Sp, type, Sp, Mapsto, Sp, body, Close);
    private static Formula FiniteAlphabet(Formula body) => All("B", Type(), Seq(
        OpenBracket, Call("Fintype", F.Id("B")), CloseBracket, Sp, body));
    private static Formula GeneralSequence(Formula body) => All("D", AnyType(),
        All("k", NatType(), All("a", Sequence(F.Id("D")), body)));
    private static Formula FiniteSequence(Formula body) => FiniteAlphabet(
        All("k", NatType(), All("a", Sequence(F.Id("B")), body)));

    private static Formula ValueFormula() => Disp(All("k", NatType(), All("ds", WordType(F.Id("k")),
        Equal(Call("Value", F.Id("k"), F.Id("ds")), Call("foldr", F.Id("ds"),
            Lambda("d", FinType(F.Id("k")), Lambda("v", NatType(),
                Add(Call("val", F.Id("d")), Mul(F.Id("k"), F.Id("v"))))), D(0))))));

    private static Formula MachineBody()
    {
        var k = F.Id("k"); var q = F.Id("q");
        return And(Le(D(2), k), Some("q", NatType(), And(Less(D(0), q),
            Some("s", FinType(q), Some("t", Arrow(FinType(q), Arrow(FinType(k), FinType(q))),
            Some("o", Arrow(FinType(q), F.Id("B")), All("n", NatType(), All("ds", WordType(k),
                Imp(Equal(Call("Value", k, F.Id("ds")), F.Id("n")),
                    Equal(Call("o", Call("Fold", F.Id("ds"), F.Id("t"), F.Id("s"))),
                        Call("a", F.Id("n"))))))))))));
    }

    private static Formula MachineFormula() => Disp(FiniteSequence(IffOf(
        Call("Machine", F.Id("k"), F.Id("a")), MachineBody())));

    private static Formula KernelFormula()
    {
        var k = F.Id("k"); var e = F.Id("e"); var r = F.Id("r");
        var membership = Some("e", NatType(), Some("r", NatType(), And(Less(r, Pow(k, e)),
            Equal(F.Id("b"), Lambda("n", NatType(), Call("a", Add(Mul(Pow(k, e), F.Id("n")), r)))))));
        var set = Seq(OpenBrace, F.Id("b"), Colon, Sp, Sequence(F.Id("D")), Sp, Mid, Sp,
            membership, CloseBrace);
        return Disp(GeneralSequence(Equal(Call("Kernel", k, F.Id("a")), set)));
    }

    private static Formula AutomaticFormula() => Disp(GeneralSequence(IffOf(
        Call("Automatic", F.Id("k"), F.Id("a")),
        And(Le(D(2), F.Id("k")), Call("Finite", Call("Kernel", F.Id("k"), F.Id("a")))))));

    private static Formula StepFormula() => Disp(All("D", AnyType(), All("q", NatType(),
        All("a", Sequence(F.Id("D")), All("b", Sequence(F.Id("D")), All("j", NatType(),
        Imp(Member(F.Id("b"), Call("Kernel", F.Id("q"), F.Id("a"))),
        Imp(Less(F.Id("j"), F.Id("q")), Member(Lambda("n", NatType(), Call("b",
            Add(Mul(F.Id("q"), F.Id("n")), F.Id("j")))),
            Call("Kernel", F.Id("q"), F.Id("a")))))))))));

    private static Formula SelfFormula() => Disp(All("D", AnyType(), All("q", NatType(),
        All("a", Sequence(F.Id("D")), Member(F.Id("a"), Call("Kernel", F.Id("q"), F.Id("a")))))));

    private static Formula EquivalenceFormula() => Disp(FiniteSequence(IffOf(
        And(Le(D(2), F.Id("k")), Call("Finite", Call("Kernel", F.Id("k"), F.Id("a")))),
        MachineBody())));
}
