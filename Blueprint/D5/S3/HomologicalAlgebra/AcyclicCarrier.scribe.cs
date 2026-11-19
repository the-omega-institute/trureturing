using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class AcyclicCarrierDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/AcyclicCarrier.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Homotopies carried by basis-indexed acyclic subcomplexes.",
        H("The augmented acyclic carrier theorem"), Blocks(
            Paragraph(Text("In every formula, C(n) and D(n) denote the objects of the given nonnegative chain complexes, dC(n):C(n+1) to C(n) and dD(n):D(n+1) to D(n) are their differentials, and B(n,b) denotes the source basis vector. The coefficient coeff(n,b,c) is B(n).repr(dC(n)(B(n+1,b)))(c). Hom and Lin denote R-linear maps, ChainMap denotes native complex morphisms, and composition is written in the usual function order. Universe parameters u, v, w and x are independent; ModuleCat(R,v) denotes the object universe v. Submodule membership and inclusion are over R. K(n,b,m) denotes the submodule field of CarrierData; Carried(K,n,m,g) means that every g(B(n,b)) lies in K(n,b,m).")),

            Node("carriers", "CarrierData", "Basis-indexed carriers",
                "For an arbitrary commutative ring R, nonnegative ModuleCat chain complexes C and D, an arbitrary family of index types I(n), and bases B(n) of C(n), a carrier assigns submodules A(n,b)(m) of D(m). The target differential preserves each carrier. If c has nonzero coefficient in the basis expansion of the boundary of b, every degree of the carrier of c lies in the corresponding degree of the carrier of b.", DescribeRole.Definition),
            Node("carried", "CarrierData.Carried", "Carried linear maps",
                "A map from C(n) to D(m) is carried when the image of every basis vector b belongs to A(n,b)(m).", DescribeRole.Definition),
            Node("acyclic", "CarrierData.Acyclic", "Augmented carrier acyclicity",
                "The augmentation may take values in an arbitrary R-module. It vanishes on boundaries. In each individual carrier, augmentation-zero elements in degree zero lift to degree one, and cycles in every positive degree lift to the next degree. No contraction or chosen lift is assumed.", DescribeRole.Definition),
            Node("boundary-support", "CarrierData.Carried.face", "Finite-support boundary extension",
                "A carried linear map sends the boundary of each source basis vector into the carrier of that vector. Expand the boundary using Basis.repr, sum only over its finite support, apply coefficient-support nesting to each term, and use closure of the target submodule under scalar multiplication and finite sums.", DescribeRole.Theorem),
            Node("subtraction", "CarrierData.Carried.sub", "Subtraction preserves bounds",
                "The difference of two maps carried in the same degrees remains carried.", DescribeRole.Theorem),
            Node("basis-lift", "basis_exists_lift", "Support-preserving basis lift",
                "For any target linear map phi and basis-indexed source map Phi, if every Phi(B(b)) has a preimage in its specified submodule, choose those preimages and extend along the source basis. The extension is carried and its composite with phi equals Phi by basis extensionality. The basis can be empty or infinite, and neither target has a basis requirement.", DescribeRole.Theorem),
            Node("positive-primitive", "CarrierData.exists_carried_primitive", "Positive-degree primitive",
                "A carried map into positive-degree cycles lifts through the target differential with the same individual carrier bounds. Extend the carrier primitives along the source basis.", DescribeRole.Theorem),
            Node("zero-primitive", "CarrierData.exists_carried_primitive0", "Augmentation-zero primitive",
                "A carried degree-zero map annihilated by the augmentation lifts to degree one with the same carrier bounds. Extend the degree-zero primitives along the source basis.", DescribeRole.Theorem),
            Node("integer-scaling", "CarrierData.Carried.comp_left", "Integer scaling preserves bounds",
                "Integer multiples of carried maps remain carried.", DescribeRole.Theorem),
            Node("boundary-precomposition", "CarrierData.Carried.d_comp", "Boundary precomposition",
                "Precomposing a carried map with the source boundary preserves the shifted carrier bound. The finite-support boundary expansion gives the bound.", DescribeRole.Theorem),
            Node("sequence", "exists_sequence", "Dependent sequence of primitive choices",
                "Given an initial state and an allowed successor for every state in every degree, dependent recursion produces a sequence satisfying the initial and successor predicates.", DescribeRole.Theorem),
            Node("component-induction", "CarrierData.exists_carried_homotopy", "Carried component induction",
                "For an arbitrary integer sign and two carried component families obeying the corresponding twisted chain equations and equal augmentation, degree induction constructs carried homotopy components. The state includes the residual cycle condition. Degree zero uses an augmentation-zero primitive; each successor subtracts the preceding homotopy on the source boundary, verifies that the residual is a cycle using the chain equations, and chooses a carrier primitive.", DescribeRole.Theorem),
            Node("native-homotopy", "exists_homotopy", "Native carried chain homotopy",
                "For every commutative ring R, arbitrary nonnegative ModuleCat chain complexes C and D, and arbitrary bases B(n) indexed by I(n), assume differential-closed basis-indexed carriers, nesting for every nonzero coefficient of each source basis boundary, and augmented acyclicity separately in every carrier. For every pair of chain maps f and g that agree after the augmentation D(0) to R and carry B(n)(b) into A(n,b)(n), there exists a native Homotopy f g whose component H.hom n (n+1) sends B(n)(b) into A(n,b)(n+1). The ring, module and index universes are arbitrary. The theorem permits zero rings, empty and infinite source bases, and non-surjective augmentations, and imposes no target basis, target projectivity, source acyclicity, global contractibility or homotopy-as-input hypothesis. The native Homotopy equations give f(0)-g(0)=dH(0), and f(n+1)-g(n+1)=dH(n+1)+H(n)d in positive degrees. The signed component construction with sign one gives the native Homotopy with exactly these carrier bounds.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration[(declaration.LastIndexOf('.') + 1)..]), H(title),
            StatementSource.FromAuthor(Statement(declaration)), AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/HomologicalAlgebra/axiommath2026acycliccarrier")),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Bind(string name, Formula type) => Seq(Open, V(name), Colon, type, Close);
    private static Formula All(Formula body, params (string Name, Formula Type)[] vars) =>
        Seq(Forall, Sp, Seq(vars.Select(v => Bind(v.Name, v.Type)).ToArray()), Comma, Sp, body);
    private static Formula Some(Formula body, params (string Name, Formula Type)[] vars) =>
        Seq(Exists, Sp, Seq(vars.Select(v => Bind(v.Name, v.Type)).ToArray()), Comma, Sp, body);
    private static Formula Both(params Formula[] terms) => Seq(terms.SelectMany((t, i) =>
        i == 0 ? new[] { Seq(Open, t, Close) } : new[] { Sp, Land, Sp, Seq(Open, t, Close) }).ToArray());
    private static Formula Imp(Formula p, Formula q) => Seq(Open, p, Close, Sp, Implies, Sp, Open, q, Close);
    private static Formula Equal(Formula p, Formula q) => Seq(p, Eq, q);
    private static Formula App(Formula f, params Formula[] xs) => Seq(f, Open,
        Seq(xs.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, x }).ToArray()), Close);
    private static Formula Comp(Formula f, Formula g) => Seq(f, Circ, Sp, g);
    private static Formula Diff(Formula f, Formula g) => Seq(f, Minus, g);
    private static Formula Inc(Formula n, int k = 1) => Seq(n, Plus, D((byte)k));
    private static Formula At(string f, Formula n) => Call(f, n);
    private static Formula BasisVector(Formula n, Formula b) => Call("B", n, b);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Integer => Seq(Mathbb, Grp(V("Z")));
    private static Formula Object(string c, Formula n) => At(c, n);
    private static Formula Lin(Formula a, Formula b) => Call("Lin", V("R"), a, b);
    private static Formula Mem(Formula z, Formula k) => Seq(z, InMacro, Sp, k);
    private static Formula Index(Formula n) => At("I", n);
    private static Formula Carrier(Formula n, Formula b, Formula m) => Call("K", n, b, m);
    private static Formula FamilyType => All(Call("Submodule", V("R"), Object("D", V("m"))),
        ("n", Nat), ("b", Index(V("n"))), ("m", Nat));
    private static Formula CarrierType => Call("CarrierData", V("B"));
    private static Formula Carried(Formula n, Formula m, Formula g) => Call("Carried", V("K"), n, m, g);
    private static Formula AugType(Formula target) => Lin(Object("D", D(0)), target);
    private static Formula AugBoundary => Equal(Comp(V("aug"), At("dD", D(0))), D(0));
    private static Formula Acyclic => Call("Acyclic", V("K"), V("aug"));
    private static Formula MemberImage(Formula n, Formula b, Formula m, Formula g) =>
        Mem(App(g, BasisVector(n, b)), Carrier(n, b, m));
    private static Formula CarriedAll(string g) => All(MemberImage(V("n"), V("b"), V("n"), At(g, V("n"))),
        ("n", Nat), ("b", Index(V("n"))));
    private static Formula Closure => All(Imp(Mem(V("z"), Carrier(V("n"), V("b"), Inc(V("m")))),
        Mem(App(At("dD", V("m")), V("z")), Carrier(V("n"), V("b"), V("m")))),
        ("n", Nat), ("b", Index(V("n"))), ("m", Nat), ("z", Object("D", Inc(V("m")))));
    private static Formula Nesting => All(Imp(Seq(Call("coeff", V("n"), V("b"), V("c")), Neq, D(0)),
        All(Seq(Carrier(V("n"), V("c"), V("m")), Subseteq, Sp,
            Carrier(Inc(V("n")), V("b"), V("m"))), ("m", Nat))),
        ("n", Nat), ("b", Index(Inc(V("n")))), ("c", Index(V("n"))));
    private static Formula AcycZero => All(Imp(Both(Mem(V("z"), Carrier(V("n"), V("b"), D(0))),
        Equal(Call("aug", V("z")), D(0))), Some(Both(
            Mem(V("y"), Carrier(V("n"), V("b"), D(1))),
            Equal(App(At("dD", D(0)), V("y")), V("z"))), ("y", Object("D", D(1))))),
        ("n", Nat), ("b", Index(V("n"))), ("z", Object("D", D(0))));
    private static Formula AcycPositive => All(Imp(Both(Mem(V("z"), Carrier(V("n"), V("b"), Inc(V("m")))),
        Equal(App(At("dD", V("m")), V("z")), D(0))), Some(Both(
            Mem(V("y"), Carrier(V("n"), V("b"), Inc(V("m"), 2))),
            Equal(App(At("dD", Inc(V("m"))), V("y")), V("z"))), ("y", Object("D", Inc(V("m"), 2))))),
        ("n", Nat), ("b", Index(V("n"))), ("m", Nat), ("z", Object("D", Inc(V("m")))));
    private static Formula Setup(Formula body, bool target = true)
    {
        Formula head = Seq(Forall, Sp, V("u"), Comma, V("v"), Comma, V("w"), Comma, Sp,
            Bind("R", Call("Type", V("u"))), Sp, OpenBracket, Call("CommRing", V("R")), CloseBracket,
            Bind("C", Call("ChainComplex", Call("ModuleCat", V("R"), V("v")), Nat)));
        Formula targetBinder = target
            ? Bind("D", Call("ChainComplex", Call("ModuleCat", V("R"), V("v")), Nat)) : Seq();
        return Seq(head, targetBinder, Bind("I", Seq(Nat, To, Sp, Call("Type", V("w")))),
            Bind("B", All(Call("Basis", Index(V("n")), V("R"), Object("C", V("n"))), ("n", Nat))),
            Comma, RowBreak, body);
    }
    private static Formula Augmented(Formula body)
    {
        Formula typed = Seq(OpenBracket, Call("AddCommGroup", V("T")), CloseBracket,
            OpenBracket, Call("Module", V("R"), V("T")), CloseBracket, Sp,
            All(body, ("aug", AugType(V("T")))));
        return All(typed, ("x", V("Universe")), ("T", Call("Type", V("x"))));
    }
    private static Formula Gather(Formula body) => Disp(Seq(Begin, Grp(V("gathered")), body, End, Grp(V("gathered"))));
    private static Formula Statement(string declaration)
    {
        Formula n = V("n"), m = V("m"), b = V("b"), g = V("g"), f = V("f");
        Formula augmentationAgreement = Equal(Comp(V("aug"), At("f", D(0))), Comp(V("aug"), At("g", D(0))));
        Formula result;
        if (declaration == "CarrierData")
        {
result = Setup(Seq(CarrierType, Colon, Eq, OpenBrace, Bind("K", FamilyType), Bar,
                    Both(Closure, Nesting), CloseBrace));
        }
        else if (declaration == "CarrierData.Carried")
        {
result = Setup(All(Seq(Carried(n, m, g), Sp, Iff, Sp,
                    All(MemberImage(n, b, m, g), ("b", Index(n)))),
                    ("K", CarrierType), ("n", Nat), ("m", Nat), ("g", Lin(Object("C", n), Object("D", m)))));
        }
        else if (declaration == "CarrierData.Acyclic")
        {
result = Setup(All(Augmented(Seq(Acyclic, Sp, Iff, Sp,
                    Both(AugBoundary, AcycZero, AcycPositive))), ("K", CarrierType)));
        }
        else if (declaration == "CarrierData.Carried.face")
        {
result = Setup(All(Imp(Carried(n, m, g), All(Mem(App(g,
                    App(At("dC", n), BasisVector(Inc(n), b))), Carrier(Inc(n), b, m)), ("b", Index(Inc(n))))),
                    ("K", CarrierType), ("n", Nat), ("m", Nat), ("g", Lin(Object("C", n), Object("D", m)))));
        }
        else if (declaration == "CarrierData.Carried.sub")
        {
result = Setup(All(Imp(Both(Carried(n, m, f), Carried(n, m, g)), Carried(n, m, Diff(f, g))),
                    ("K", CarrierType), ("n", Nat), ("m", Nat), ("f", Lin(Object("C", n), Object("D", m))),
                    ("g", Lin(Object("C", n), Object("D", m)))));
        }
        else if (declaration == "basis_exists_lift")
        {
result = Setup(All(Imp(All(Mem(App(V("Phi"), BasisVector(n, b)),
                    Call("map", Call("KY", b), V("phi"))), ("b", Index(n))),
                    Some(Both(All(Mem(App(V("Psi"), BasisVector(n, b)), Call("KY", b)), ("b", Index(n))),
                        Equal(Comp(V("phi"), V("Psi")), V("Phi"))),
                        ("Psi", Lin(Object("C", n), V("Y"))))),
                    ("n", Nat), ("Y", Call("ModuleCat", V("R"), V("v"))),
                    ("Z", Call("ModuleCat", V("R"), V("v"))),
                    ("KY", Seq(Index(n), To, Sp, Call("Submodule", V("R"), V("Y")))),
                    ("phi", Lin(V("Y"), V("Z"))), ("Phi", Lin(Object("C", n), V("Z")))), false);
        }
        else if (declaration == "CarrierData.exists_carried_primitive" || declaration == "CarrierData.exists_carried_primitive0")
        {
bool zero = declaration.EndsWith("primitive0", StringComparison.Ordinal);
                Formula inputDegree = zero ? D(0) : Inc(m);
                Formula outputDegree = zero ? D(1) : Inc(m, 2);
                Formula cycle = zero ? Equal(Comp(V("aug"), V("Phi")), D(0))
                    : Equal(Comp(At("dD", m), V("Phi")), D(0));
                Formula primitiveConclusion = Some(Both(Carried(n, outputDegree, V("Psi")),
                    Equal(Comp(At("dD", inputDegree), V("Psi")), V("Phi"))),
                    ("Psi", Lin(Object("C", n), Object("D", outputDegree))));
                Formula primitiveBody = Imp(Both(Acyclic, Carried(n, inputDegree, V("Phi")), cycle), primitiveConclusion);
                Formula primitiveQuantified = zero
                    ? All(primitiveBody, ("n", Nat), ("Phi", Lin(Object("C", n), Object("D", inputDegree))))
                    : All(primitiveBody, ("n", Nat), ("m", Nat), ("Phi", Lin(Object("C", n), Object("D", inputDegree))));
                result = Setup(All(Augmented(primitiveQuantified), ("K", CarrierType)));
        }
        else if (declaration == "CarrierData.Carried.comp_left")
        {
result = Setup(All(Imp(Carried(n, m, g), Carried(n, m, Seq(V("e"), Cdot, Sp, g))),
                    ("K", CarrierType), ("n", Nat), ("m", Nat), ("g", Lin(Object("C", n), Object("D", m))), ("e", Integer)));
        }
        else if (declaration == "CarrierData.Carried.d_comp")
        {
result = Setup(All(Imp(Carried(n, m, g), Carried(Inc(n), m, Comp(g, At("dC", n)))),
                    ("K", CarrierType), ("n", Nat), ("m", Nat), ("g", Lin(Object("C", n), Object("D", m)))));
        }
        else if (declaration == "exists_sequence")
        {
Formula initialExists = Some(Call("initial", V("q")), ("q", At("State", D(0))));
                Formula nextExists = All(Some(Call("step", m, V("q"), V("t")),
                    ("t", At("State", Inc(m)))), ("m", Nat), ("q", At("State", m)));
                Formula sequenceType = All(At("State", m), ("m", Nat));
                Formula sequenceLaw = Both(Call("initial", Call("seq", D(0))),
                    All(Call("step", m, Call("seq", m), Call("seq", Inc(m))), ("m", Nat)));
                Formula sequenceConclusion = Some(sequenceLaw, ("seq", sequenceType));
                result = All(Imp(Both(initialExists, nextExists), sequenceConclusion),
                    ("s", V("Universe")), ("State", Seq(Nat, To, Sp, Call("Type", V("s")))),
                    ("initial", Seq(At("State", D(0)), To, Sp, V("Prop"))),
                    ("step", All(Seq(At("State", m), To, Sp, At("State", Inc(m)), To, Sp, V("Prop")), ("m", Nat))));
        }
        else if (declaration == "CarrierData.exists_carried_homotopy")
        {
Formula twisted(string map) => All(Equal(Comp(At("dD", n), At(map, Inc(n))),
                    Seq(V("e"), Cdot, Sp, Grp(Comp(At(map, n), At("dC", n))))), ("n", Nat));
                Formula family = All(Lin(Object("C", n), Object("D", n)), ("n", Nat));
                Formula homFamily = All(Lin(Object("C", n), Object("D", Inc(n))), ("n", Nat));
                Formula signedPremises = Both(Acyclic, twisted("f"), twisted("g"),
                    CarriedAll("f"), CarriedAll("g"), augmentationAgreement);
                Formula homZero = Equal(Diff(At("f", D(0)), At("g", D(0))),
                    Comp(At("dD", D(0)), At("h", D(0))));
                Formula homSuccessor = All(Equal(Diff(At("f", Inc(n)), At("g", Inc(n))),
                    Seq(Comp(At("dD", Inc(n)), At("h", Inc(n))), Plus,
                        V("e"), Cdot, Sp, Grp(Comp(At("h", n), At("dC", n))))), ("n", Nat));
                Formula signedConclusion = Some(Both(All(Carried(n, Inc(n), At("h", n)), ("n", Nat)),
                    homZero, homSuccessor), ("h", homFamily));
                Formula signedBody = All(Imp(signedPremises, signedConclusion),
                    ("e", Integer), ("f", family), ("g", family));
                result = Setup(All(Augmented(signedBody), ("K", CarrierType)));
        }
        else if (declaration == "exists_homotopy")
        {
Formula mainPremises = Both(Closure, Nesting, AugBoundary, AcycZero, AcycPositive,
                    augmentationAgreement, CarriedAll("f"), CarriedAll("g"));
                Formula mainSupport = All(MemberImage(n, b, Inc(n), Call("H", n, Inc(n))),
                    ("n", Nat), ("b", Index(n)));
                Formula mainConclusion = Some(mainSupport, ("H", Call("Homotopy", f, g)));
                result = Setup(All(Imp(mainPremises, mainConclusion),
                    ("K", FamilyType), ("aug", AugType(V("R"))),
                    ("f", Call("ChainMap", V("C"), V("D"))), ("g", Call("ChainMap", V("C"), V("D")))));
        }
        else throw new InvalidOperationException("Unknown acyclic carrier declaration.");
        return Gather(result);
    }
}
