import { afterAll } from 'bun:test'
import {
  isolateManifestDirectoriesForTheRun,
  removeManifestDirectoriesOfTheRun,
} from './helpers/private-manifest-directory.js'

// Before any test file is loaded, so no wrap or clean-up of the run reaches the
// user's real manifest directories. The stand-ins are removed after the last
// test file.
isolateManifestDirectoriesForTheRun()
afterAll(removeManifestDirectoriesOfTheRun)
