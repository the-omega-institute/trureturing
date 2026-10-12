using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class QuadraticCompanionDefectDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/QuadraticCompanionDefect.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Scope(Formula body, params Formula.BoundVariable[] variables) => All(body,
        [B("A", I("Type")), B("inst", Call("AddCommGroup", I("A"))), .. variables]);
    private static Formula Row(Formula n) => Call("Function", Call("Fin", n), I("A"));
    private static Formula N => Call("add", I("n"), Num(2));
    private static Formula V => Row(N);
    private static Formula J => Call("AddMonoidHom", I("A"), I("A"));
    private static Formula Apply(Formula f, Formula x) => Call("apply", f, x);
    private static Formula Domain(Formula v) => Apply(Call("domainEquiv", I("n")), v);
    private static Formula Co(Formula y) => Apply(Call("codomainEquiv", I("J"), I("n")), y);
    private static DocumentBlock Def(string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
    private static DocumentBlock Thm(string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-')), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral elimination of an identity-plus-square companion using two initial coordinates.",
        H("Quadratic companion defect"), Blocks(
            Paragraph(Text("A is any additive commutative group and J:A->A any additive homomorphism. "
                + "Rows have n+2 coordinates indexed by Fin(n+2). first(v)=v(0), "
                + "second(v)=v((0:Fin(n+1)).succ), and skipSum(v,j)=v(j.succ.succ)+v(j.castSucc.castSucc). "
                + "All shears and recurrences use only addition and subtraction. No field, division by two, "
                + "finite state-space or torsion-free hypothesis is imposed.")),
            Def("reconstruct", "A two-coordinate integral recurrence",
                Scope(Call("hasType", Call("reconstruct", I("n"), I("a"), I("b"), I("t")), V),
                    B("n", I("Nat")), B("a", I("A")), B("b", I("A")), B("t", Row(I("n")))),
                "At n=0 the row is (a,b). At n+1 it is Fin.cons a applied to reconstruct n "
                + "with initial values b and t(0)-a and remaining input t(j.succ). Therefore "
                + "every tail satisfies v(j+2)+v(j)=t(j), including all boundary cases."),
            Def("domainEquiv", "Two free values and all two-step sums",
                Scope(Call("hasType", Call("domainEquiv", I("n")), Call("AddEquiv", V,
                    Call("Prod", Call("Prod", I("A"), I("A")), Row(I("n"))))), B("n", I("Nat"))),
                "The forward map is v -> ((first(v),second(v)), j -> skipSum(v,j)); "
                + "its inverse is reconstruct. The reconstruction identities prove both inverse "
                + "equations on the entire additive group."),
            Def("prefixSum", "Sum omitting the rightmost coordinate",
                Scope(Call("hasType", Call("prefixSum", I("n"), I("v")), I("A")),
                    B("n", I("Nat")), B("v", V)),
                "prefixSum n v is the sum over j:Fin(n+1) of v(j.castSucc). "
                + "It is the sum of the coordinates that remain after one companion shift."),
            Def("companion", "The actual two-step boundary and tail equations",
                Scope(Call("hasType", Call("companion", I("J"), I("n")), Call("AddMonoidHom", V, V)),
                    B("J", J), B("n", I("Nat"))),
                "Write S=sum v and P=prefixSum n v. The output is "
                + "(a+J(J(S)+P), b+J(S), j -> skipSum(v,j)). This is identity plus the square "
                + "of the reset companion whose first transition coordinate is J(sum v). "
                + "J need not be invertible for the definition or general elimination."),
            Def("codomainEquiv", "Remove inhomogeneous tail contributions",
                Scope(Call("hasType", Call("codomainEquiv", I("J"), I("n")), Call("AddEquiv", V,
                    Call("Prod", Call("Prod", I("A"), I("A")), Row(I("n"))))),
                    B("J", J), B("n", I("Nat"))),
                "Given y, let t(j)=y(j.succ.succ), and p=reconstruct n 0 0 t. "
                + "Subtract the first two coordinates of companion J n p from (first(y),second(y)); "
                + "retain t. The inverse adds this same correction and uses Fin.cons twice. "
                + "The shear is independent of the two free domain values."),
            Def("boundary", "The homogeneous two-dimensional boundary map",
                Scope(Call("hasType", Call("boundary", I("J"), I("n"), I("a"), I("b")),
                    Call("Prod", I("A"), I("A"))), B("J", J), B("n", I("Nat")),
                    B("a", I("A")), B("b", I("A"))),
                "Evaluate the first two companion coordinates on reconstruct n a b 0. "
                + "The homogeneous row follows the actual period-four recurrence a,b,-a,-b. "
                + "No rational eigenspace replaces its integer coordinates."),
            Thm("eliminate", "Exact additive normal form of the quadratic defect",
                Scope(Equal(Co(Apply(Call("companion", I("J"), I("n")), I("v"))),
                    Call("pair", Call("boundary", I("J"), I("n"), Call("first", I("v")),
                        Call("second", I("v"))), Call("secondProjection", Domain(I("v"))))),
                    B("J", J), B("n", I("Nat")), B("v", V)),
                "Separate v into its homogeneous reconstruction and its zero-head inhomogeneous "
                + "reconstruction. Additivity shows that the codomain correction cancels exactly "
                + "the latter's boundary contribution, while the remaining tails are identity. "
                + "The domain and codomain equivalences were constructed separately."),
            Thm("boundary_three_mod_four", "Two copies of identity plus an involution",
                Scope(Equal(Call("boundary", I("J"), Call("add", Call("mul", Num(4), I("m")), Num(1)),
                    I("a"), I("b")), Call("pair",
                    Call("add", Call("add", I("a"), I("b")), Apply(I("J"), Call("add", I("a"), I("b")))),
                    Call("add", I("b"), Apply(I("J"), I("b"))))),
                    B("J", J), B("hJ", All(Equal(Apply(I("J"), Apply(I("J"), I("x"))), I("x")),
                        B("x", I("A")))), B("m", I("Nat")), B("a", I("A")), B("b", I("A"))),
                "The carrier length is (4m+1)+2=4m+3. Its homogeneous row has total sum b "
                + "and prefix sum a+b, proved by a four-step recurrence and induction on m. "
                + "If J(J(x))=x for every x, the boundary is ((id+J)(a+b),(id+J)(b)). "
                + "The integral shear (a,b)->(a+b,b) is invertible, so these are two independent "
                + "copies of id+J. This includes m=0, carrier length three."),
            Paragraph(Text("Escape audit status. The original generic theorems eliminate and "
                + "boundary_three_mod_four and their mirrored Reg proofs compile. Their source bindings "
                + "remain declared_unresolved: IE-C050 ClosedTruthReadout, reason=unclassified_form, "
                + "rule=source.params for eliminate and rule=source.state_binder for "
                + "boundary_three_mod_four. The missing classified source bindings and certificates "
                + "are tracked at https://github.com/the-omega-institute/trureturing/issues/15897. "
                + "Their escape audits are unfinished; this issue supplies neither proof nor "
                + "declared_validated status.")))));
}
