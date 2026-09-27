import { afterAll } from 'bun:test'
import {
  isolateManifestDirectoriesForTheRun,
  removeManifestDirectoriesOfTheRun,
} from './helpers/private-manifest-directory.js'

// Before any test file is loaded, so that no wrap and no clean-up of the run
// reaches the directories the user's own sandboxes keep their manifests in. A
// hook here belongs to the run and not to a file: the stand-ins go after the
// last test file.
isolateManifestDirectoriesForTheRun()
afterAll(removeManifestDirectoriesOfTheRun)
