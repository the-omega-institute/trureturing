using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;
internal sealed class ResetQ4UnitCubesDocument : IScribeDocumentDefinition
{
    private static Formula I(string s) => FormulaDsl.Id(s);
    private static Formula.BoundVariable B(string s, Formula t) => new(FormulaIdentifier.Create(s), t);
    private static Formula All(Formula f, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.ForAll, [..v], f);
    private static Formula Ex(Formula f, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.Exists, [..v], f);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Pow(string u, Formula n) => Call("pow", I(u), n);
    private static Formula Val(string i) => Call("val", I(i));
    private static Formula Units(string order) => Call("Units", Call(order, Num(4)));
    private static Formula PlusForm => Equal(I("u"), Multiply(Multiply(Pow("alpha", Val("i")), Pow("Bplus", Val("j"))), Pow("v", Num(3))));
    private static Formula MinusForm(string u, string v) => Equal(I(u), Multiply(Pow("Bminus", Val("k")), Pow(v, Num(3))));
    private static DocumentBlock Entry(string n, string h, Formula f, string p) => Describe.Lean(
        DescribeId.Create(n.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/ResetQ4UnitCubes." + n),
        H(h), StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(p))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent finite cubic characters saturate the Dirichlet rank of the original quartic reset orders.",
        H("Cube normal forms in the quartic reset orders"), Blocks(
            Describe.Lean(
                DescribeId.Create("existing-six-resetq4unitcubes-residuecharacter"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/ResetQ4UnitCubes.residueCharacter"),
                H("Expose the oriented character of the literal common residue units"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Expose the existing oriented readout cK as an additive homomorphism from the common residue units into ZMod 3. It selects the native exponent in the integral unit factorization."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("existing-six-resetq4unitcubes-residuecharacter-plus-factorization"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/ResetQ4UnitCubes.residueCharacter_plus_factorization"),
                H("Read the residue coordinate of a supplied integral cube factorization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the stated plus-order unit factorization, the native common residue character reads the one-plus-time exponent j in ZMod 3. The same j is carried into the original centralizer factorization."))),
                DescribeRole.Theorem),


            Paragraph(Text("Use the literal original orders Plus(4)=Int[X]/(X^4-X^3-X^2-X-1) "
                + "and Minus(4)=Int[X]/(X^4+X^3+X^2+X+1). alpha and beta are the classes of X "
                + "as units, and Bplus=1+alpha, Bminus=1+beta. Their integral inverse polynomials "
                + "are X^3-X^2-X-1, X^4, 2-X+2X^2-X^3 and -X-X^3, respectively. "
                + "The field of the plus polynomial has signature (2,1); the minus field has "
                + "signature (0,2). Positive plus roots are classified by the existing Perron "
                + "reciprocal-sum theorem; a strictly monotone polynomial in the negative variable "
                + "gives its unique negative root. The primitive fifth root excludes real minus "
                + "places. A real embedding excludes plus three-torsion; simultaneous primitive "
                + "third and fifth roots would force degree at least eight on the minus side. "
                + "Both actual fields have degree four, so Dirichlet ranks are two and one.")),
            Entry("plus_cube_normal_form", "Every original plus-order unit has a two-coordinate cube form",
                All(Ex(PlusForm, B("i", Call("Fin", Num(3))), B("j", Call("Fin", Num(3))), B("v", Units("Plus"))), B("u", Units("Plus"))),
                "Gauss divisibility embeds the monic original order into its quartic field, "
                + "and integral elements land in the integer ring. FiniteKernelModThree applies "
                + "to the actual image lattice, with a finite torsion kernel, and gives dimension "
                + "at most two for original cube classes. It does not infer cube-quotient "
                + "injectivity from the order embedding. The actual common mod-two quotient "
                + "is the sixteen-element field. Its oriented cubic character cK and the "
                + "alpha=5 mod-seven character cSeven have matrix [[0,1],[1,0]] on alpha,Bplus. "
                + "Thus the two classes are independent. Their synthesis map attains the "
                + "dimension bound and is surjective. The kernel of the original quotient "
                + "returns v in Units(Plus(4)) itself."),
            Entry("minus_cube_normal_form", "Every original minus-order unit has a one-coordinate cube form",
                All(Ex(MinusForm("u", "v"), B("k", Call("Fin", Num(3))), B("v", Units("Minus"))), B("u", Units("Minus"))),
                "The same descent bounds the original minus cube quotient by one. The common "
                + "finite-field character takes Bminus to one, so this class is independent "
                + "and spans. Quotient equality produces the cube preimage in Units(Minus(4)), "
                + "rather than only in the surrounding number field. No fundamental-unit "
                + "or maximal-order identification is required."),
            Entry("compatible_cube_normal_forms", "Compatible original units have the same common cube coordinate",
                All(Imp(Equal(Call("UnitsMap", Call("rplus", Num(4)), I("u")),
                        Call("UnitsMap", Call("rminus", Num(4)), I("w"))),
                    Ex(And(PlusForm, And(MinusForm("w", "t"),
                            Equal(Call("castZMod3", Val("j")), Call("castZMod3", Val("k"))))),
                        B("i", Call("Fin", Num(3))), B("j", Call("Fin", Num(3))),
                        B("k", Call("Fin", Num(3))), B("v", Units("Plus")), B("t", Units("Minus")))),
                    B("u", Units("Plus")), B("w", Units("Minus"))),
                "The hypothesis is literal equality of the residue units under rplus(4) and "
                + "rminus(4). Applying cK to both original-order normal forms kills cubes and "
                + "alpha, leaving j=k in ZMod(3). Both cube roots remain in their respective "
                + "original orders. These component normal forms do not assert exhaustion of "
                + "a history representation image or the original-h SGCC factorization."))));
}
