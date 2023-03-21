/-!
# Registration

* fill in your name, github username, zulip handle, and url for your lab repo.
* check details with `#eval details?`
* the command `lake exe lab1` should now work and give details about your registration.
* commit and push your changes to your repo.
-/
def name?: Option String := "Suryansh Shrivastava"
def github?: Option String := "Shraze97"
def zulip?: Option String := "Suryansh Shrivastava"
def lab_repo?: Option String := "https://github.com/Shraze97/Lab-Assignments.git"

def details? : Option String := do
  let name ← name?
  let github ← github?
  let zulip ← zulip?
  let lab_repo ← lab_repo?
  pure $ s!"Name: {name}; Gihub username:{github}; Zulip handle: {zulip}; Lab repo url: {lab_repo}"

#eval details?
