//! A pretty printer for Eunoia proofs.
use crate::translation::eunoia_ast::*;
use std::io;

// TODO: struct for future actual formatting concerns
/// A formatter for S-expressions.
pub struct SExpFormatter<'a> {
    sink: &'a mut dyn io::Write,
}

impl<'a> SExpFormatter<'a> {
    pub fn new(sink: &'a mut dyn io::Write) -> Self {
        SExpFormatter { sink }
    }

    // Prints an s-expression with properly formatted concrete syntax, and
    // separating it from surrounding s-expressions.
    fn write_s_expr(&mut self, tag: &str, args: &[String]) -> io::Result<()> {
        if args.is_empty() {
            // S-expression is a constant
            write!(self.sink, "{}", tag)?;
        } else {
            // {not args.is_empty()}
            // S-expression has the form (tag arg1 ...)
            write!(self.sink, "(")?;
            write!(self.sink, "{}", tag)?;
            // TODO: how to propagate errors from within the lambda abstraction?
            args.iter().for_each(|arg| {
                let _ = write!(self.sink, " {}", arg);
            });

            write!(self.sink, ")")?;
        };

        writeln!(self.sink)?;

        Ok(())
    }
}

pub struct EunoiaPrinter<'a> {
    // TODO: why is it `&'a mut dyn io::Write` in ast::printer.rs?
    // Where to write.
    formatted_sink: SExpFormatter<'a>,
    // term_indices: Option<IndexMap<Rc<Term>, usize>>,
    // term_sharing_variable_prefix: &'static str,
    // global_vars: HashSet<Rc<Term>>,
    // defined_constants: HashMap<Rc<Term>, String>,
    // smt_lib_strict: bool,
}

pub trait PrintProof {
    fn write_proof(&mut self, proof: &EunoiaProof) -> io::Result<()>;
}

impl<'a> PrintProof for EunoiaPrinter<'a> {
    /// Formatted proof printing.
    fn write_proof(&mut self, proof: &EunoiaProof) -> io::Result<()> {
        let mut tag: String;
        let mut args: Vec<String>;

        // TODO: some generic way of doing this? maybe with macros?
        for command in proof {
            match command {
                EunoiaCommand::Assume { name, term } => {
                    tag = "assume".to_owned();
                    args = vec![name.clone(), EunoiaPrinter::term_to_concrete_syntax(term)];
                }

                EunoiaCommand::AssumePush { name, term } => {
                    tag = "assume-push".to_owned();

                    args = vec![name.clone(), EunoiaPrinter::term_to_concrete_syntax(term)];
                }

                EunoiaCommand::DeclareConst { name, eunoia_type, attrs } => {
                    tag = "declare-const".to_owned();

                    args = Vec::new();

                    args.push(name.clone());
                    args.push(EunoiaPrinter::term_to_concrete_syntax(eunoia_type));

                    attrs.iter().for_each(|attr| {
                        args.push(EunoiaPrinter::cons_attr_to_concrete_syntax(attr));
                    });
                }

                EunoiaCommand::DeclareType { name, kind } => {
                    tag = "declare-type".to_owned();

                    args = Vec::new();

                    args.push(name.clone());

                    args.append(&mut EunoiaPrinter::eunoia_list_to_concrete_syntax(
                        kind,
                        &EunoiaPrinter::type_to_concrete_syntax,
                    ));
                }

                EunoiaCommand::Define { name, typed_params, term, attrs } => {
                    tag = "define".to_owned();

                    args = Vec::new();

                    args.push(name.clone());

                    args.append(&mut EunoiaPrinter::eunoia_list_to_concrete_syntax(
                        typed_params,
                        &EunoiaPrinter::typed_param_to_concrete_syntax,
                    ));

                    args.push(EunoiaPrinter::term_to_concrete_syntax(term));

                    attrs.iter().for_each(|attr| {
                        args.push(EunoiaPrinter::define_attr_to_concrete_syntax(attr));
                    });
                }

                EunoiaCommand::Program {
                    name,
                    typed_params,
                    params,
                    ret,
                    body,
                } => {
                    tag = "program".to_owned();

                    args = Vec::new();
                    // Program name.
                    args.push(name.clone());
                    // Typed params.
                    args.append(&mut EunoiaPrinter::eunoia_list_to_concrete_syntax(
                        typed_params,
                        &EunoiaPrinter::typed_param_to_concrete_syntax,
                    ));
                    // Formal parameters.
                    args.append(&mut EunoiaPrinter::eunoia_list_to_concrete_syntax(
                        params,
                        &EunoiaPrinter::type_to_concrete_syntax,
                    ));
                    // Return type.
                    args.push(EunoiaPrinter::type_to_concrete_syntax(ret));
                    // Program's body.
                    args.append(&mut EunoiaPrinter::eunoia_list_to_concrete_syntax(
                        body,
                        &Box::new(|tuple: &(EunoiaTerm, EunoiaTerm)| {
                            "(".to_owned()
                                + &EunoiaPrinter::term_to_concrete_syntax(&tuple.0)
                                + " "
                                + &EunoiaPrinter::term_to_concrete_syntax(&tuple.1)
                                + ")"
                        }),
                    ));
                }

                EunoiaCommand::SetLogic { name } => {
                    tag = "set-logic".to_owned();

                    args = vec![name.clone()];
                }

                EunoiaCommand::Step {
                    name,
                    conclusion_clause,
                    rule,
                    premises,
                    arguments,
                } => {
                    tag = "step".to_owned();

                    args = Vec::new();

                    args.push(name.clone());

                    if let Some(term) = conclusion_clause {
                        args.push(EunoiaPrinter::term_to_concrete_syntax(term));
                    };

                    args.push(":rule ".to_owned() + &rule.clone());

                    let EunoiaList { list } = premises;

                    if !list.is_empty() {
                        args.push(":premises".to_owned());
                        args.append(&mut EunoiaPrinter::eunoia_list_to_concrete_syntax(
                            premises,
                            &EunoiaPrinter::term_to_concrete_syntax,
                        ));
                    }

                    let EunoiaList { list } = arguments;
                    if !list.is_empty() {
                        args.push(":args".to_owned());
                        args.append(&mut EunoiaPrinter::eunoia_list_to_concrete_syntax(
                            arguments,
                            &EunoiaPrinter::term_to_concrete_syntax,
                        ));
                    }
                }

                EunoiaCommand::StepPop {
                    name,
                    conclusion_clause,
                    rule,
                    premises,
                    arguments,
                } => {
                    tag = "step-pop".to_owned();

                    args = Vec::new();

                    args.push(name.clone());

                    if let Some(term) = conclusion_clause {
                        args.push(EunoiaPrinter::term_to_concrete_syntax(term));
                    };

                    // TODO: rule names are not equal: let -> let_elim
                    args.push(":rule ".to_owned() + &rule.clone());

                    let EunoiaList { list } = premises;
                    if !list.is_empty() {
                        args.push(":premises".to_owned());
                        args.append(&mut EunoiaPrinter::eunoia_list_to_concrete_syntax(
                            premises,
                            &EunoiaPrinter::term_to_concrete_syntax,
                        ));
                    };

                    let EunoiaList { list } = arguments;

                    if !list.is_empty() {
                        args.push(":args".to_owned());
                        args.append(&mut EunoiaPrinter::eunoia_list_to_concrete_syntax(
                            arguments,
                            &EunoiaPrinter::term_to_concrete_syntax,
                        ));
                    }
                }

                EunoiaCommand::DeclareSort { .. } => {
                    tag = "declare-sort".to_owned();

                    args = vec![];
                }
            };

            self.formatted_sink.write_s_expr(&tag, &args)?;
        }

        Ok(())
    }
}

impl<'a> EunoiaPrinter<'a> {
    pub fn new(dest: SExpFormatter<'a>) -> Self {
        Self { formatted_sink: dest }
    }

    fn cons_attr_to_concrete_syntax(attr: &EunoiaConsAttr) -> String {
        match attr {
            EunoiaConsAttr::RightAssoc => ":right-assoc".to_owned(),

            _ => ":right-assoc".to_owned(),
        }
    }

    fn term_to_concrete_syntax(term: &EunoiaTerm) -> String {
        let mut ret;

        match term {
            EunoiaTerm::Numeral(n) => {
                ret = n.to_string();
            }

            EunoiaTerm::Decimal(r) => {
                ret = String::from("");

                if r.is_negative() {
                    ret += "(- ";
                }
                if r.is_integer() {
                    ret += &(r.clone().abs().to_string() + ".0");
                } else {
                    ret += &("(/ ".to_owned()
                        + &r.numer().clone().abs().to_string()
                        + ".0 "
                        + &r.denom().to_string()
                        + ".0");
                }
                if r.is_negative() {
                    ret += ")";
                }
            }

            EunoiaTerm::Rational(n, d) => {
                ret = n.to_string() + "/" + &d.to_string();
            }

            EunoiaTerm::Id(name) => {
                ret = name.clone();
            }

            EunoiaTerm::Type(some_type) => {
                ret = EunoiaPrinter::type_to_concrete_syntax(some_type);
            }

            EunoiaTerm::True => {
                ret = "true".to_owned();
            }

            EunoiaTerm::False => {
                ret = "false".to_owned();
            }

            EunoiaTerm::App(symbol, params) => {
                ret = "(".to_owned() + &symbol.clone();

                params.iter().for_each(|param| {
                    ret += " ";
                    ret += &EunoiaPrinter::term_to_concrete_syntax(param);
                });

                ret += ")";
            }

            EunoiaTerm::Op(operator, params) => {
                ret = "(".to_owned() + &EunoiaPrinter::operator_to_concrete_syntax(operator);

                params.iter().for_each(|param| {
                    ret += " ";
                    ret += &EunoiaPrinter::term_to_concrete_syntax(param);
                });

                ret += ")";
            }

            EunoiaTerm::String(string) => {
                ret = "\"".to_owned() + &string.clone() + "\"";
            }

            EunoiaTerm::List(terms) => {
                ret = "(".to_owned();

                terms.iter().for_each(|term| {
                    ret += " ";
                    ret += &EunoiaPrinter::term_to_concrete_syntax(term);
                });

                ret += " )";
            }

            EunoiaTerm::Var(name, sort) => {
                ret = "(".to_owned();
                ret += " ";
                ret += &name.clone();
                ret += " ";
                ret += &EunoiaPrinter::term_to_concrete_syntax(sort);
                ret += " )";
            }
        }

        ret
    }

    fn type_to_concrete_syntax(some_type: &EunoiaType) -> String {
        let mut ret: String;

        match some_type {
            EunoiaType::Bool => {
                ret = "Bool".to_owned();
            }

            EunoiaType::Type => {
                ret = "Type".to_owned();
            }

            EunoiaType::Real => {
                ret = "Real".to_owned();
            }

            EunoiaType::Name(name) => {
                ret = name.clone();
            }

            EunoiaType::Fun(kind_params, dom, codom) => {
                ret = "(-> ".to_owned();

                kind_params.iter().for_each(|kind| {
                    ret += &EunoiaPrinter::kind_param_to_concrete_syntax(kind);
                    ret += " ";
                });

                dom.iter().for_each(|some_type| {
                    ret += &EunoiaPrinter::type_to_concrete_syntax(some_type);
                    ret += " ";
                });

                ret += &EunoiaPrinter::type_to_concrete_syntax(codom);
                ret += ")";
            }
        }

        ret
    }

    fn typed_param_to_concrete_syntax(param: &EunoiaTypedParam) -> String {
        let mut ret = "(".to_owned();

        let EunoiaTypedParam { name, eunoia_type, attrs } = param;

        ret += &name.clone();
        ret += " ";
        ret += &EunoiaPrinter::type_to_concrete_syntax(eunoia_type);

        attrs.iter().for_each(|attr| {
            ret += " ";
            ret += &EunoiaPrinter::cons_attr_to_concrete_syntax(attr);
        });

        ret += ")";

        ret
    }

    fn define_attr_to_concrete_syntax(attr: &EunoiaDefineAttr) -> String {
        match attr {
            EunoiaDefineAttr::Type(some_type) => {
                ":type ".to_owned() + &EunoiaPrinter::type_to_concrete_syntax(some_type)
            }
        }
    }

    fn type_attr_to_concrete_syntax(attr: &EunoiaTypeAttr) -> String {
        match attr {
            EunoiaTypeAttr::Var(name) => ":var ".to_owned() + &name.clone(),

            EunoiaTypeAttr::Implicit => ":implicit".to_owned(),

            EunoiaTypeAttr::Requires(lhs, rhs) => {
                ((":requires (".to_owned() + &EunoiaPrinter::term_to_concrete_syntax(lhs))
                    + " "
                    + &EunoiaPrinter::term_to_concrete_syntax(rhs))
                    + ")"
            }
        }
    }

    fn kind_param_to_concrete_syntax(attr: &EunoiaKindParam) -> String {
        let mut ret = "(! ".to_owned();

        match attr {
            EunoiaKindParam::KindParam(some_type, attrs) => {
                ret += &EunoiaPrinter::type_to_concrete_syntax(some_type);

                attrs.iter().for_each(|attr| {
                    ret += " ";
                    ret += &EunoiaPrinter::type_attr_to_concrete_syntax(attr);
                });
            }
        }

        ret += ")";

        ret
    }

    fn operator_to_concrete_syntax(op: &EunoiaOperator) -> String {
        match op {
            EunoiaOperator::Xor => "xor".to_owned(),

            EunoiaOperator::Not => "not".to_owned(),

            // NOTE: these are the symbols used in theory.eo
            EunoiaOperator::Eq => "=".to_owned(),

            EunoiaOperator::GreaterThan => ">".to_owned(),

            EunoiaOperator::GreaterEq => ">=".to_owned(),

            EunoiaOperator::LessThan => "<".to_owned(),

            EunoiaOperator::LessEq => "<=".to_owned(),
        }
    }

    /// Pseudo-map over a `EunoiaList`<T>
    fn eunoia_list_to_concrete_syntax<T>(
        eunoia_list: &EunoiaList<T>,
        to_concrete: &dyn Fn(&T) -> String,
    ) -> Vec<String> {
        let mut ret = Vec::new();

        ret.push("(".to_owned());

        let EunoiaList { list } = eunoia_list;
        list.iter().for_each(|elem| ret.push(to_concrete(elem)));

        ret.push(")".to_owned());

        ret
    }
}
